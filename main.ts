import {
  App,
  Editor,
  ItemView,
  MarkdownView,
  Notice,
  Plugin,
  PluginSettingTab,
  Setting,
  WorkspaceLeaf,
  setIcon,
} from "obsidian";
import { EditorState, StateEffect, StateField } from "@codemirror/state";
import type { Extension, Range } from "@codemirror/state";
import {
  Decoration,
  DecorationSet,
  EditorView,
} from "@codemirror/view";

const VIEW_TYPE = "novel-tracker-view";
const SEP_MARK = "···";

// 默认配置
const DELETE_SETTLE_MS = 1200;
const DEFAULT_IDLE_THRESHOLD_MS = 5000;

// LCS 单元格上限，超过后改用行级回落算法，避免长文卡死
const LCS_CELL_LIMIT = 4_000_000;
// 版本记录上限（只影响“版本演变”，不影响总览）
const MAX_VERSIONS = 600;
// 保存节流
const SAVE_DEBOUNCE_MS = 800;
// 视图刷新节流
const VIEW_DEBOUNCE_MS = 120;

// 计时竞速默认值
const DEFAULT_RIVAL_NAME = "Killer";
const DEFAULT_RIVAL_SPEED = 1000; // 字/小时
const MIN_RIVAL_SPEED = 100;
const MAX_RIVAL_SPEED = 20000;

/**
 * Word 计字规则：汉字（含扩展区、兼容区、部首）每字 1；全角标点各 1；
 * 英文按空格分词；连续数字为 1；破折号不计；……计 1。
 */
export function countWords(text: string): number {
  let s = text.replace(/^---[\s\S]*?---\s*/, "");
  s = s.replace(/```[\s\S]*?```/g, " ");
  s = s.replace(/%%[\s\S]*?%%/g, "");
  s = s.replace(/<!--[\s\S]*?-->/g, " ");
  s = s.replace(/<[^>]*>/g, " ");
  s = s.replace(/[#*`~_>|]/g, " ");
  s = s.normalize("NFC");
  s = s.replace(/—/g, "");
  s = s.replace(/[“”‘’"]?…{2,}[“”‘’"]?/g, "…");
  s = s.replace(/([一-龥　-〿＀-￯])(?=[a-zA-Z0-9])/g, "$1 ");
  s = s.replace(/([a-zA-Z0-9])(?=[一-龥　-〿＀-￯])/g, "$1 ");
  s = s.replace(/^[\s]*[^\w\s\p{Script=Han}　-〿！-￮‘-‟…—][\s]*$/gmu, "");
  s = s.replace(/[\s　]+/g, " ").trim();

  const cjkRegex = /[\p{Script=Han}、-〿！-￮‘-‟…—]/gu;
  const cjkMatch = s.match(cjkRegex) || [];
  const remaining = s.replace(cjkRegex, " ");
  const blocks = remaining.split(/\s+/).filter(Boolean);
  const enMatch = blocks.filter((block) => /[a-zA-Z0-9]/.test(block));
  return cjkMatch.length + enMatch.length;
}

interface SessionState {
  running: boolean;
  startedAt: number;
  elapsedMs: number;
  baseInput: number;
  baseFinal: number;
}

interface TrackerSettings {
  rivalName: string;
  rivalSpeed: number;
  statusBar: boolean;
}

interface SessionStats {
  running: boolean;
  elapsedMs: number;
  ownChars: number;
  rawChars: number;
  keptChars: number;
  rawRate: number;
  actualRate: number;
  rivalChars: number;
  /** 自己（最终保留）减对手，正数即反超 */
  gap: number;
}

interface VersionRecord {
  timestamp: number;
  content: string;
}

interface PauseRecord {
  timestamp: number;
  duration: number;
}

interface TrackerStats {
  totalInput: number;
  totalDelete: number;
  versionCount: number;
  finalChars: number;
  retentionRate: number;
}

type DiffOp = { type: "equal" | "delete" | "insert"; value: string };

/**
 * 总览里的一个“字”记录。
 * 记录只增不减：alive 只表示它现在是否还在正文里，不会被移除。
 */
interface CharRecord {
  c: string;
  alive: boolean;
  /** 是否是本次追踪期间由用户输入的（用于统计，不计插件启动前已有内容） */
  input: boolean;
}

interface FileState {
  chars: CharRecord[];       // 展示顺序，只增不减
  alive: CharRecord[];       // 与当前正文一一对应的存活记录
  current: string;           // 过滤后的当前正文
  versions: VersionRecord[];
  pauses: PauseRecord[];
  totalInput: number;
  totalDelete: number;
  lastActiveTime: number;
  idleRecorded: boolean;
  /** 当前是否处于一次删除动作中（删除停止后存档一个版本） */
  deleting: boolean;
}

interface PersistedFileState {
  chars: [string, 0 | 1, 0 | 1][];
  versions: { t: number; c: string }[];
  pauses: { t: number; d: number }[];
  totalInput: number;
  totalDelete: number;
}

interface PersistedData {
  version: number;
  files: Record<string, PersistedFileState>;
  session?: { r: 0 | 1; s: number; e: number; bi: number; bf: number };
  settings?: { name: string; speed: number; sb?: 0 | 1; hs?: 0 | 1 };
}

/**
 * 虎码/英文噪声：写作正文里所有 ASCII 字母片段都会被整段剥掉。
 * 这样 1 位、2-4 位、5 位以上、大小写混合的编码都不会进入任何统计与渲染。
 */
const ASCII_LETTER_RUN = /[A-Za-z]+/g;
const VALID_CHAR = /[\p{Script=Han}\u3000-\u303F\uFF00-\uFFEF]/u;
const SEPARATOR_LINE_RE = /^\s*···\s*$/;
const SEPARATOR_TOGGLE = StateEffect.define<boolean>();

export default class NovelWriteTrackerPlugin extends Plugin {
  private fileStates: Map<string, FileState> = new Map();
  private activePath: string | null = null;
  private active: FileState | null = null;

  // 删除结束后存档版本的防抖计时器（每个文件一个）
  private deleteTimers: Map<FileState, number> = new Map();

  // 空闲检测
  private idleThresholdMs: number = DEFAULT_IDLE_THRESHOLD_MS;
  private idleTimer: number | null = null;

  // 保存 / 刷新
  private saveTimer: number | null = null;
  private viewTimer: number | null = null;
  private loaded = false;
  // 编辑器内隐藏 ··· 分隔行（眼睛按钮）
  private separatorHidden = false;
  private openingView = false;


  // 状态栏字数（Word 规则）
  private statusBarEl: HTMLElement | null = null;
  private statusEditor: Editor | null = null;
  private statusTimer: number | null = null;

  // 计时 / 竞速
  private session: SessionState = {
    running: false,
    startedAt: 0,
    elapsedMs: 0,
    baseInput: 0,
    baseFinal: 0,
  };
  private trackerSettings: TrackerSettings = {
    rivalName: DEFAULT_RIVAL_NAME,
    rivalSpeed: DEFAULT_RIVAL_SPEED,
    statusBar: true,
  };

  async onload() {
    await this.loadPersisted();

    this.registerView(VIEW_TYPE, (leaf) => new TrackerView(leaf, this));
    this.registerEditorExtension(this.buildSeparatorField());
    this.addSettingTab(new TrackerSettingTab(this.app, this));
    this.statusBarEl = this.addStatusBarItem();

    this.addRibbonIcon("pencil", "写作删改追踪", () => {
      void this.activateView();
    });

    this.registerEvent(
      this.app.workspace.on("editor-change", (editor, info) => {
        const area = this.extractWritingArea(editor.getValue());
        if (area === null) return;
        const path =
          info?.file?.path ?? this.app.workspace.getActiveFile()?.path ?? null;
        if (!path) return;
        this.ingest(path, this.stripNoise(area));
      })
    );

    this.registerEvent(
      this.app.workspace.on("active-leaf-change", () => {
        const editor = this.app.workspace.activeEditor?.editor;
        const file = this.app.workspace.getActiveFile();
        if (!editor || !file) return;
        const area = this.extractWritingArea(editor.getValue());
        if (area === null) return;
        const tracked = this.stripNoise(area);
        if (file.path !== this.activePath) this.setActiveFile(file.path, tracked);
      })
    );

    this.registerEvent(
      this.app.vault.on("rename", (file, oldPath) => {
        const state = this.fileStates.get(oldPath);
        if (!state) return;
        this.fileStates.delete(oldPath);
        this.fileStates.set(file.path, state);
        if (this.activePath === oldPath) this.activePath = file.path;
        this.scheduleSave();
      })
    );

    this.registerEvent(
      this.app.workspace.on("editor-change", (editor) => {
        this.statusEditor = editor;
        this.scheduleStatusUpdate();
      }),
    );
    this.registerEvent(
      this.app.workspace.on("active-leaf-change", () => {
        this.updateStatusEditor();
        this.scheduleStatusUpdate();
      }),
    );
    this.registerEvent(
      this.app.workspace.on("file-open", () => {
        this.updateStatusEditor();
        this.scheduleStatusUpdate();
      }),
    );
    this.registerDomEvent(document, "selectionchange", () => this.scheduleStatusUpdate());

    this.startIdleTimer();

    this.app.workspace.onLayoutReady(() => {
      this.updateStatusEditor();
      this.renderStatusBar();
      this.loaded = true;
      const editor = this.app.workspace.activeEditor?.editor;
      const file = this.app.workspace.getActiveFile();
      if (!editor || !file) return;
      const area = this.extractWritingArea(editor.getValue());
      if (area === null) return;
      this.setActiveFile(file.path, this.stripNoise(area));
    });
  }

  /** 只保留一个面板：已存在时聚焦，不存在时才创建。 */
  private async activateView() {
    if (this.openingView) return;

    const existing = this.app.workspace.getLeavesOfType(VIEW_TYPE)[0];
    if (existing) {
      this.app.workspace.setActiveLeaf(existing, { focus: true });
      await this.app.workspace.revealLeaf(existing);
      return;
    }

    this.openingView = true;
    try {
      const leaf = this.app.workspace.getRightLeaf(false);
      if (!leaf) return;
      await leaf.setViewState({ type: VIEW_TYPE, active: true });
      await this.app.workspace.revealLeaf(leaf);
    } finally {
      this.openingView = false;
    }
  }

  // ==================== 噪声过滤 ====================

  /** 去掉所有 ASCII 英文字母片段（虎码编码、临时拼音等）。 */
  private stripNoise(text: string): string {
    return text.replace(ASCII_LETTER_RUN, "");
  }

  private isValidChar(c: string): boolean {
    return VALID_CHAR.test(c);
  }


  // ==================== 工具：HTML转义 ====================

  private escapeHtml(text: string): string {
    return text
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;");
  }

  // ==================== 字符级差分 ====================

  private lcsDiff(aArr: string[], bArr: string[]): DiffOp[] {
    const m = aArr.length;
    const n = bArr.length;
    const dp: Uint32Array[] = [];
    for (let i = 0; i <= m; i++) dp.push(new Uint32Array(n + 1));

    for (let i = 1; i <= m; i++) {
      const row = dp[i];
      const prev = dp[i - 1];
      for (let j = 1; j <= n; j++) {
        if (aArr[i - 1] === bArr[j - 1]) {
          row[j] = prev[j - 1] + 1;
        } else {
          row[j] = prev[j] >= row[j - 1] ? prev[j] : row[j - 1];
        }
      }
    }

    const ops: DiffOp[] = [];
    let i = m;
    let j = n;
    while (i > 0 && j > 0) {
      if (aArr[i - 1] === bArr[j - 1]) {
        ops.unshift({ type: "equal", value: aArr[i - 1] });
        i--;
        j--;
      } else if (dp[i - 1][j] >= dp[i][j - 1]) {
        ops.unshift({ type: "delete", value: aArr[i - 1] });
        i--;
      } else {
        ops.unshift({ type: "insert", value: bArr[j - 1] });
        j--;
      }
    }
    while (i > 0) {
      ops.unshift({ type: "delete", value: aArr[i - 1] });
      i--;
    }
    while (j > 0) {
      ops.unshift({ type: "insert", value: bArr[j - 1] });
      j--;
    }
    return this.mergeOps(ops);
  }

  private mergeOps(ops: DiffOp[]): DiffOp[] {
    const merged: DiffOp[] = [];
    for (const op of ops) {
      if (!op.value) continue;
      const last = merged[merged.length - 1];
      if (last && last.type === op.type) last.value += op.value;
      else merged.push({ ...op });
    }
    return merged;
  }

  /** 行级回落：超大改动时避免 O(n²) 卡死。 */
  private lineFallback(coreA: string[], coreB: string[]): DiffOp[] {
    const splitKeep = (arr: string[]): string[] => {
      const tokens = arr.join("").match(/[^\n]*\n|[^\n]+$/g);
      return tokens ?? [];
    };
    return this.lcsDiff(splitKeep(coreA), splitKeep(coreB));
  }

  /** 先裁掉公共前后缀，只对中间段做 LCS；无身份歧义，反复编辑同一位置也稳定。 */
  private charDiff(a: string, b: string): DiffOp[] {
    if (a === b) return [];
    const A = [...a];
    const B = [...b];

    let p = 0;
    const maxP = Math.min(A.length, B.length);
    while (p < maxP && A[p] === B[p]) p++;

    let s = 0;
    while (s < maxP - p && A[A.length - 1 - s] === B[B.length - 1 - s]) s++;

    const coreA = A.slice(p, A.length - s);
    const coreB = B.slice(p, B.length - s);

    let coreOps: DiffOp[];
    if (coreA.length * coreB.length <= LCS_CELL_LIMIT) {
      coreOps = this.lcsDiff(coreA, coreB);
    } else {
      coreOps = this.lineFallback(coreA, coreB);
    }

    const ops: DiffOp[] = [];
    if (p > 0) ops.push({ type: "equal", value: A.slice(0, p).join("") });
    ops.push(...coreOps);
    if (s > 0) ops.push({ type: "equal", value: A.slice(A.length - s).join("") });
    return this.mergeOps(ops);
  }

  // ==================== 核心：总览的追加式同步 ====================

  private createState(text: string): FileState {
    const chars: CharRecord[] = [...text].map((c) => ({
      c,
      alive: true,
      input: false,
    }));
    const state: FileState = {
      chars: [...chars],
      alive: [...chars],
      current: text,
      versions: [{ timestamp: Date.now(), content: text }],
      pauses: [],
      totalInput: 0,
      totalDelete: 0,
      lastActiveTime: Date.now(),
      idleRecorded: false,
      deleting: false,
    };
    return state;
  }

  /**
   * 把正文从 state.current 同步到 newText。
   * 规则：
   *  - 新增字符：插到当前光标位置对应的位置，永久保留；
   *  - 删除字符：只把 alive 置 false，不删除记录；
   *  - 同一位置重打刚删掉的字：复活原记录，不产生重复幽灵。
   */
  private applyText(
    state: FileState,
    newText: string,
  ): { changed: boolean; inserted: boolean; deleted: boolean } {
    if (newText === state.current) {
      return { changed: false, inserted: false, deleted: false };
    }
    let insertedCount = 0;
    let deletedCount = 0;

    const ops = this.charDiff(state.current, newText);
    let ci = 0;

    for (const op of ops) {
      if (op.type === "equal") {
        ci += op.value.length;
        continue;
      }

      if (op.type === "delete") {
        deletedCount += op.value.length;
        const removed = state.alive.splice(ci, op.value.length);
        for (const rec of removed) {
          rec.alive = false;
          if (rec.input && this.isValidChar(rec.c)) state.totalDelete++;
        }
        continue;
      }

      // insert
      const chars = [...op.value];
      insertedCount += chars.length;
      const nextAlive = ci < state.alive.length ? state.alive[ci] : null;
      const pos = nextAlive ? state.chars.indexOf(nextAlive) : state.chars.length;

      // 找到插入点左侧连续的“已删除”记录，尝试复活其中与本次输入匹配的后缀
      let runStart = pos;
      while (runStart - 1 >= 0 && !state.chars[runStart - 1].alive) runStart--;
      const runLen = pos - runStart;

      let reviveCount = 0;
      const maxK = Math.min(runLen, chars.length);
      for (let k = maxK; k > 0; k--) {
        let ok = true;
        for (let x = 0; x < k; x++) {
          if (state.chars[runStart + runLen - k + x].c !== chars[x]) {
            ok = false;
            break;
          }
        }
        if (ok) {
          reviveCount = k;
          break;
        }
      }

      const revived: CharRecord[] = [];
      for (let x = 0; x < reviveCount; x++) {
        const rec = state.chars[runStart + runLen - reviveCount + x];
        rec.alive = true;
        rec.input = true;
        if (this.isValidChar(rec.c)) state.totalInput++;
        revived.push(rec);
      }

      const fresh: CharRecord[] = chars.slice(reviveCount).map((c) => {
        const rec: CharRecord = { c, alive: true, input: true };
        if (this.isValidChar(c)) state.totalInput++;
        return rec;
      });

      if (fresh.length) state.chars.splice(pos, 0, ...fresh);
      const inserted = revived.concat(fresh);
      state.alive.splice(ci, 0, ...inserted);
      ci += inserted.length;
    }

    state.current = newText;
    return {
      changed: true,
      inserted: insertedCount > 0,
      deleted: deletedCount > 0,
    };
  }

  // ==================== 文件状态管理 ====================

  private setActiveFile(path: string, tracked: string) {
    let state = this.fileStates.get(path);
    if (!state) {
      state = this.createState(tracked);
      this.fileStates.set(path, state);
    } else {
      const pre = state.current;
      const summary = this.applyText(state, tracked);
      if (summary.changed) this.afterChange(state, pre, summary.deleted);
    }

    this.activePath = path;
    this.active = state;
    state.lastActiveTime = Date.now();
    state.idleRecorded = false;

    this.scheduleSave();
    this.scheduleViewUpdate();
  }

  private ingest(path: string, tracked: string) {
    let state = this.fileStates.get(path);
    if (!state) {
      state = this.createState(tracked);
      this.fileStates.set(path, state);
    }

    const switched = path !== this.activePath;
    this.activePath = path;
    this.active = state;

    state.lastActiveTime = Date.now();
    state.idleRecorded = false;

    const pre = state.current;
    const summary = this.applyText(state, tracked);
    if (switched || summary.changed) this.scheduleViewUpdate();

    if (summary.changed) {
      this.scheduleSave();
      this.afterChange(state, pre, summary.deleted);
    }
  }

  /**
   * 版本策略：新增不存档；只删改时才记录。
   *  - 删除开始的瞬间：把“删除前累计内容”存为一个版本；
   *  - 删除停止 DELETE_SETTLE_MS 后：把删完的内容存为下一个版本；
   *  - 两次删除之间的新增内容，会在下一次删除开始时被一并存档。
   */
  private afterChange(state: FileState, preText: string, deleted: boolean) {
    if (!deleted) return;

    if (!state.deleting) {
      // 删除动作开始：先补存删除前的版本（含此前的所有新增）
      this.pushVersion(state, preText);
    }
    this.armDeleteSettle(state);
  }

  private armDeleteSettle(state: FileState) {
    state.deleting = true;
    const old = this.deleteTimers.get(state);
    if (old) clearTimeout(old);
    const timer = window.setTimeout(() => {
      this.deleteTimers.delete(state);
      state.deleting = false;
      this.commitVersion(state);
    }, DELETE_SETTLE_MS);
    this.deleteTimers.set(state, timer);
  }

  private cancelDeleteSettle(state: FileState) {
    const timer = this.deleteTimers.get(state);
    if (timer) clearTimeout(timer);
    this.deleteTimers.delete(state);
    state.deleting = false;
  }


  private pushVersion(state: FileState, content: string) {
    const last = state.versions[state.versions.length - 1];
    if (last && last.content === content) return;

    state.versions.push({ timestamp: Date.now(), content });
    if (state.versions.length > MAX_VERSIONS) {
      state.versions.splice(0, state.versions.length - MAX_VERSIONS);
    }
    this.scheduleSave();
    this.scheduleViewUpdate();
  }


  private commitVersion(state: FileState) {
    this.pushVersion(state, state.current);
  }

  // ==================== 提取写作区域 ====================

  private extractWritingArea(text: string): string | null {
    const lines = text.split("\n");
    const sepIndexes: number[] = [];
    lines.forEach((line, idx) => {
      if (line.trim() === SEP_MARK) sepIndexes.push(idx);
    });
    if (sepIndexes.length < 2) return null;
    const start = sepIndexes[0] + 1;
    const end = sepIndexes[1];
    return lines.slice(start, end).join("\n");
  }

  // ==================== 统计数据 ====================
  // ==================== 计时 / 竞速 ====================


  public getSessionStats(): SessionStats {
    const stats = this.calculateStats();
    const elapsedMs = this.session.running
      ? this.session.elapsedMs + Math.max(0, Date.now() - this.session.startedAt)
      : this.session.elapsedMs;
    const rawChars = Math.max(0, stats.totalInput - this.session.baseInput);
    const keptChars = Math.max(0, stats.finalChars - this.session.baseFinal);
    const hours = elapsedMs / 3_600_000;
    // 前 3 秒样本太短，速率会飙到无意义的大数
    const stable = elapsedMs >= 3000;
    const rawRate = stable ? Math.round(rawChars / hours) : 0;
    const actualRate = stable ? Math.round(keptChars / hours) : 0;
    const rivalChars = Math.floor(hours * this.trackerSettings.rivalSpeed);

    return {
      running: this.session.running,
      elapsedMs,
      rawChars,
      keptChars,
      rawRate,
      actualRate,
      rivalChars,
      ownChars: stats.finalChars,
      gap: stats.finalChars - rivalChars,
    };
  }

  public async toggleSession(): Promise<void> {
    if (this.session.running) {
      this.stopSession();
      return;
    }

    // 无论有没有旧数据，点击后直接开始；旧记录保留，不做导出或清空询问


    const stats = this.calculateStats();
    this.session = {
      running: true,
      startedAt: Date.now(),
      elapsedMs: 0,
      baseInput: stats.totalInput,
      baseFinal: stats.finalChars,
    };
    this.scheduleSave();
    this.updateAllViews();
  }

  private stopSession(): void {
    if (!this.session.running) return;
    this.session.elapsedMs += Math.max(0, Date.now() - this.session.startedAt);
    this.session.running = false;
    this.session.startedAt = 0;
    this.scheduleSave();
    this.updateAllViews();
  }


  // ==================== 统计数据 ====================
  public calculateStats(): TrackerStats {
    const state = this.active;
    if (!state) {
      return {
        totalInput: 0,
        totalDelete: 0,
        versionCount: 0,
        finalChars: 0,
        retentionRate: 0,
      };
    }

    // 核心统计的字数统一走 countWords（与状态栏同一规则）。
    // 只统计“输入过”的字：正文原有内容 input=false，删掉它不算累计删除。
    const inputRecords = state.chars.filter((rec) => rec.input);
    let inputText = "";
    let aliveInputText = "";
    let deletedText = "";
    for (const rec of inputRecords) {
      inputText += rec.c;
      if (rec.alive) aliveInputText += rec.c;
      else deletedText += rec.c;
    }

    const totalInput = countWords(inputText);
    const totalDelete = countWords(deletedText);
    const aliveInput = countWords(aliveInputText);
    const finalChars = aliveInput;
    const retentionRate =
      totalInput > 0
        ? Math.min(100, Math.round((aliveInput / totalInput) * 1000) / 10)
        : 0;

    return {
      totalInput,
      totalDelete,
      versionCount: state.versions.length,
      finalChars,
      retentionRate,
    };
  }

  // ==================== 整体删改总览（只增不减） ====================

  public getActiveFileName(): string {
    if (!this.activePath) return "未激活文件";
    const parts = this.activePath.split("/");
    return parts[parts.length - 1] || this.activePath;
  }

  public isSeparatorHidden(): boolean {
    return this.separatorHidden;
  }

  /** 眼睛按钮：用 CM6 装饰隐藏编辑器里的 ··· 分隔行。 */
  public setSeparatorHidden(hidden: boolean) {
    this.separatorHidden = hidden;
    const effect = SEPARATOR_TOGGLE.of(hidden);
    for (const leaf of this.app.workspace.getLeavesOfType("markdown")) {
      const view = leaf.view;
      if (!(view instanceof MarkdownView)) continue;
      const editor = view.editor as Editor & { cm?: EditorView };
      editor.cm?.dispatch({ effects: effect });
    }
    this.updateAllViews();
    this.scheduleSave();
  }

  /** CM6 StateField：文档/选区变化时重建分隔行装饰，眼睛按钮用 effect 切换。 */
  private buildSeparatorField(): Extension {
    const plugin = this;
    return StateField.define<DecorationSet>({
      create(state) {
        return plugin.separatorHidden
          ? plugin.buildSeparatorDecorations(state)
          : Decoration.none;
      },
      update(decorations, tr) {
        const toggle = tr.effects.find((effect) =>
          effect.is(SEPARATOR_TOGGLE),
        );
        if (toggle) {
          return toggle.value
            ? plugin.buildSeparatorDecorations(tr.state)
            : Decoration.none;
        }
        if (!plugin.separatorHidden) return Decoration.none;
        if (tr.docChanged || tr.selection !== undefined) {
          return plugin.buildSeparatorDecorations(tr.state);
        }
        return decorations;
      },
      provide: (field) => EditorView.decorations.from(field),
    });
  }

  /** 未持有光标的 ··· 分隔行连同相邻换行整行 replace；光标所在行保留原文以便编辑。 */
  private buildSeparatorDecorations(state: EditorState): DecorationSet {
    const ranges: Range<Decoration>[] = [];
    let pendingFrom = -1;
    let pendingTo = -1;

    const flush = () => {
      if (pendingFrom < 0) return;
      ranges.push(Decoration.replace({}).range(pendingFrom, pendingTo));
      pendingFrom = -1;
      pendingTo = -1;
    };

    for (let i = 1; i <= state.doc.lines; i++) {
      const line = state.doc.line(i);
      if (!SEPARATOR_LINE_RE.test(line.text)) continue;

      const hasCursor = state.selection.ranges.some(
        (range) => range.from <= line.to && range.to >= line.from,
      );
      if (hasCursor) continue;

      // 优先吞掉分隔行后的换行；末行则吞掉前一个换行。
      // 文档只有一行 ··· 时没有可吞的换行，只替换标记本身。
      let from = line.from;
      let to = line.to;
      if (i < state.doc.lines) {
        to = state.doc.line(i + 1).from;
      } else if (i > 1) {
        from = state.doc.line(i - 1).to;
      }

      if (pendingFrom < 0) {
        pendingFrom = from;
        pendingTo = to;
      } else if (from <= pendingTo) {
        pendingTo = Math.max(pendingTo, to);
      } else {
        flush();
        pendingFrom = from;
        pendingTo = to;
      }
    }
    flush();

    return Decoration.set(ranges, true);
  }

  public getOverviewDiffHtml(): string {
    const state = this.active;
    if (!state || state.chars.length === 0) {
      return "<span style='color:var(--text-muted)'>暂无输入</span>";
    }

    const rows: string[] = [];
    let line: CharRecord[] = [];

    const flush = () => {
      const html = this.renderCharSegments(line);
      const stats = this.computeLineStats(line);
      if (html) {
        rows.push(
          `<div class="ov-line"><div class="ov-text">${html}</div>` +
            `<div class="ov-stats">增${stats.input}字·删${stats.deleted}字·存留率${stats.retention}%</div></div>`,
        );
      } else {
        rows.push(`<div class="ov-line ov-blank"></div>`);
      }
      line = [];
    };

    for (const rec of state.chars) {
      line.push(rec);
      if (rec.c === "\n") flush();
    }
    if (line.length) flush();

    return rows.join("");
  }

  /** 把一行记录渲染成 绿色(存活)/红色删除线(已删) 片段；换行由行结构表达。 */
  private renderCharSegments(records: CharRecord[]): string {
    const parts: string[] = [];
    let buf = "";
    let bufAlive: boolean | null = null;

    const flushBuf = () => {
      if (!buf) return;
      const html = this.escapeHtml(buf);
      parts.push(
        bufAlive
          ? `<span class="diff-insert">${html}</span>`
          : `<span class="diff-delete">${html}</span>`,
      );
      buf = "";
    };

    for (const rec of records) {
      if (rec.c === "\n") continue;
      if (bufAlive === null) bufAlive = rec.alive;
      if (rec.alive !== bufAlive) {
        flushBuf();
        bufAlive = rec.alive;
      }
      buf += rec.c;
    }
    flushBuf();
    return parts.join("");
  }

  /** 单行的“增/删/留存率”，用于总览每行末尾的小字。 */
  private computeLineStats(records: CharRecord[]): {
    input: number;
    deleted: number;
    retention: number;
  } {
    // 行内小字也走 countWords，与核心统计、状态栏保持同一口径
    let inputText = "";
    let aliveInputText = "";
    let deletedText = "";

    for (const rec of records) {
      if (rec.c === "\n") continue;
      if (rec.input) {
        inputText += rec.c;
        if (rec.alive) aliveInputText += rec.c;
        else deletedText += rec.c;
      }
    }

    const input = countWords(inputText);
    const deleted = countWords(deletedText);
    const aliveInput = countWords(aliveInputText);

    return {
      input,
      deleted,
      retention:
        input > 0
          ? Math.min(100, Math.round((aliveInput / input) * 1000) / 10)
          : 0,
    };
  }
  /** 行级 LCS；超大版本直接整段替换，避免 O(n²) 卡死。 */
  private diffLineOps(a: string[], b: string[]): DiffOp[] {
    if (a.length * b.length > LCS_CELL_LIMIT) {
      const ops: DiffOp[] = [];
      for (const value of a) ops.push({ type: "delete", value });
      for (const value of b) ops.push({ type: "insert", value });
      return ops;
    }

    const m = a.length;
    const n = b.length;
    const dp: Uint32Array[] = [];
    for (let i = 0; i <= m; i++) dp.push(new Uint32Array(n + 1));
    for (let i = 1; i <= m; i++) {
      const row = dp[i];
      const prev = dp[i - 1];
      for (let j = 1; j <= n; j++) {
        if (a[i - 1] === b[j - 1]) row[j] = prev[j - 1] + 1;
        else row[j] = Math.max(prev[j], row[j - 1]);
      }
    }

    const ops: DiffOp[] = [];
    let i = m;
    let j = n;
    while (i > 0 && j > 0) {
      if (a[i - 1] === b[j - 1]) {
        ops.unshift({ type: "equal", value: a[i - 1] });
        i--;
        j--;
      } else if (dp[i - 1][j] >= dp[i][j - 1]) {
        ops.unshift({ type: "delete", value: a[i - 1] });
        i--;
      } else {
        ops.unshift({ type: "insert", value: b[j - 1] });
        j--;
      }
    }
    while (i > 0) {
      i--;
      ops.unshift({ type: "delete", value: a[i] });
    }
    while (j > 0) {
      j--;
      ops.unshift({ type: "insert", value: b[j] });
    }
    return ops;
  }

  /** 把前后两版裁到公共前后缀之内，只返回改动行；成对的删/插行合并成一行对比。 */
  private getChangedLines(prev: string, curr: string): Array<{ oldLine?: string; newLine?: string }> {
    const a = prev.split("\n");
    const b = curr.split("\n");

    let p = 0;
    const maxP = Math.min(a.length, b.length);
    while (p < maxP && a[p] === b[p]) p++;

    let s = 0;
    while (s < maxP - p && a[a.length - 1 - s] === b[b.length - 1 - s]) s++;

    const coreA = a.slice(p, a.length - s);
    const coreB = b.slice(p, b.length - s);
    const ops = this.diffLineOps(coreA, coreB);
    const changes: Array<{ oldLine?: string; newLine?: string }> = [];

    for (let i = 0; i < ops.length; i++) {
      if (ops[i].type === "equal") continue;
      const deleted: string[] = [];
      const inserted: string[] = [];
      while (i < ops.length && ops[i].type !== "equal") {
        if (ops[i].type === "delete") deleted.push(ops[i].value);
        else inserted.push(ops[i].value);
        i++;
      }

      const paired = Math.min(deleted.length, inserted.length);
      for (let k = 0; k < paired; k++) {
        changes.push({ oldLine: deleted[k], newLine: inserted[k] });
      }
      for (let k = paired; k < deleted.length; k++) {
        changes.push({ oldLine: deleted[k] });
      }
      for (let k = paired; k < inserted.length; k++) {
        changes.push({ newLine: inserted[k] });
      }
    }
    return changes;
  }

  private renderVersionLine(
    change: { oldLine?: string; newLine?: string },
    inlineStyle: boolean,
  ): string {
    const delOpen = inlineStyle
      ? '<span style="color:#c25a5a;text-decoration:line-through">'
      : '<span class="diff-delete">';
    const insOpen = inlineStyle
      ? '<span style="color:#4a9d6e">'
      : '<span class="diff-insert">';

    let inner = "";
    if (change.oldLine !== undefined && change.newLine !== undefined) {
      for (const op of this.charDiff(change.oldLine, change.newLine)) {
        const text = this.escapeHtml(op.value);
        if (op.type === "delete") inner += `${delOpen}${text}</span>`;
        else if (op.type === "insert") inner += `${insOpen}${text}</span>`;
        else inner += text;
      }
    } else if (change.oldLine !== undefined) {
      const text = this.escapeHtml(change.oldLine) || "&nbsp;";
      inner = `${delOpen}${text}</span>`;
    } else {
      const text = this.escapeHtml(change.newLine ?? "") || "&nbsp;";
      inner = `${insOpen}${text}</span>`;
    }

    if (!inner) inner = "&nbsp;";
    const styleAttr = inlineStyle ? ' style="white-space:pre-wrap"' : "";
    return `<div class="version-line"${styleAttr}>${inner}</div>`;
  }

  private versionDiffHtml(prev: string, curr: string, inlineStyle: boolean): string {
    return this.getChangedLines(prev, curr)
      .map((change) => this.renderVersionLine(change, inlineStyle))
      .join("");
  }

  // ==================== 版本演变列表 ====================
  public getVersionListHtml(): string {
    const state = this.active;
    if (!state || state.versions.length < 2) {
      return "<span style='color:var(--text-muted)'>暂无版本演变记录</span>";
    }

    const blocks: string[] = [];
    let pauseIndex = 0;

    for (let i = 1; i < state.versions.length; i++) {
      const time = new Date(state.versions[i].timestamp).toLocaleTimeString();
      const prev = state.versions[i - 1].content;
      const curr = state.versions[i].content;

      // 只呈现真正改动过的行，行内再做字符级高亮
      const diffHtml = this.versionDiffHtml(prev, curr, false);
      if (!diffHtml) continue;

      while (
        pauseIndex < state.pauses.length &&
        state.pauses[pauseIndex].timestamp < state.versions[i].timestamp
      ) {
        const pause = state.pauses[pauseIndex];
        const sec = Math.round(pause.duration / 1000);
        blocks.push(`<div class="pause-block">⏸ 停顿 ${sec} 秒</div>`);
        pauseIndex++;
      }



      blocks.push(`
        <div class="version-block">
          <div class="version-title">版本 ${i} · ${time}</div>
          <div class="diff-content">${diffHtml}</div>
        </div>
      `);
    }

    return blocks.length
      ? blocks.join("")
      : "<span style='color:var(--text-muted)'>暂无版本演变记录</span>";
  }

  // ==================== 导出 Markdown ====================

  /** 导出当前文件的全部分析记录到同目录下的 md 文件。 */
  public async exportMarkdown(): Promise<void> {
    const state = this.active;
    if (!state || !this.activePath) {
      new Notice("请先打开一篇笔记");
      return;
    }
    if (state.chars.length === 0) {
      new Notice("当前文件还没有可导出的记录");
      return;
    }

    const full = this.activePath;
    const slash = full.lastIndexOf("/");
    const folder = slash >= 0 ? full.slice(0, slash) : "";
    const base = (slash >= 0 ? full.slice(slash + 1) : full).replace(/\.md$/i, "");
    const stamp = this.formatStamp(new Date());
    const prefix = folder ? `${folder}/` : "";

    let target = `${prefix}${base}-删改追踪-${stamp}.md`;
    let n = 2;
    while (this.app.vault.getAbstractFileByPath(target)) {
      target = `${prefix}${base}-删改追踪-${stamp}-${n}.md`;
      n++;
    }

    try {
      await this.app.vault.create(target, this.buildExportMarkdown(state, base));
      new Notice(`已导出：${target}`);
    } catch (err) {
      new Notice(`导出失败：${String(err)}`);
    }
  }

  private formatStamp(d: Date): string {
    const p = (v: number) => String(v).padStart(2, "0");
    return (
      `${d.getFullYear()}${p(d.getMonth() + 1)}${p(d.getDate())}` +
      `-${p(d.getHours())}${p(d.getMinutes())}${p(d.getSeconds())}`
    );
  }
  private formatElapsed(ms: number): string {
    const total = Math.floor(Math.max(0, ms) / 1000);
    const h = Math.floor(total / 3600);
    const m = Math.floor((total % 3600) / 60);
    const s = total % 60;
    const p = (v: number) => String(v).padStart(2, "0");
    return `${p(h)}:${p(m)}:${p(s)}`;
  }

  private buildExportMarkdown(state: FileState, base: string): string {
    const stats = this.calculateStats();
    const md: string[] = [];

    md.push(`# 写作删改追踪 · ${base}`, "");
    md.push(`导出时间：${new Date().toLocaleString()}`, "");
    md.push("## 核心数据", "");
    md.push(`- 累计输入：${stats.totalInput} 字`);
    md.push(`- 累计删除：${stats.totalDelete} 字`);
    md.push(`- 最终保留：${stats.finalChars} 字`);
    md.push(`- 留存率：${stats.retentionRate}%`);
    md.push(`- 版本记录：${stats.versionCount} 条`, "");

    const session = this.getSessionStats();
    if (session.elapsedMs > 0) {
      md.push("## 本次写作", "");
      md.push(`- 写作计时：${this.formatElapsed(session.elapsedMs)}`);
      md.push(`- 原始时速：${session.rawRate} 字/时`);
      md.push(`- 实际时速：${session.actualRate} 字/时`);
      md.push(`- 本次输入：${session.rawChars} 字`);
      md.push(`- 本次保留：${session.keptChars} 字`);
      md.push(`- 对手已写：${session.rivalChars} 字`);
      const gapText =
        session.gap >= 0 ? `反超 ${session.gap} 字` : `落后 ${-session.gap} 字`;
      md.push(`- 当前差距：${gapText}`, "");
    }

    md.push("## 整体删改总览", "");
    md.push(
      '> <span style="color:#4a9d6e">绿色</span> = 仍在正文；' +
        '<span style="color:#c25a5a;text-decoration:line-through">红色删除线</span> = 写过又删掉（永久保留）',
      "",
    );

    let line: CharRecord[] = [];
    const flushLine = () => {
      const text = this.renderLineMarkdown(line);
      const s = this.computeLineStats(line);
      if (text) {
        md.push(text, "");
        md.push(`<small>增${s.input}字·删${s.deleted}字·存留率${s.retention}%</small>`, "");
      }
      line = [];
    };
    for (const rec of state.chars) {
      line.push(rec);
      if (rec.c === "\n") flushLine();
    }
    if (line.length) flushLine();

    md.push("## 版本演变详情", "");
    if (state.versions.length < 2) {
      md.push("暂无版本演变记录", "");
    } else {
      let pauseIndex = 0;
      for (let i = 1; i < state.versions.length; i++) {
        while (
          pauseIndex < state.pauses.length &&
          state.pauses[pauseIndex].timestamp < state.versions[i].timestamp
        ) {
          const pause = state.pauses[pauseIndex];
          if (pause.duration >= 120) {
            md.push(`> ⏸ 停顿 ${Math.round(pause.duration / 60)} 分`, "");
          }
          pauseIndex++;
        }
        const prev = state.versions[i - 1].content;
        const curr = state.versions[i].content;
        const diffHtml = this.versionDiffHtml(prev, curr, true);
        if (!diffHtml) continue;

        const time = new Date(state.versions[i].timestamp).toLocaleString();
        md.push(`### 版本 ${i} · ${time}`, "");
        md.push(diffHtml, "");
      }
    }

    return md.join("\n") + "\n";
  }

  private renderLineMarkdown(records: CharRecord[]): string {
    let out = "";
    let buf = "";
    let alive: boolean | null = null;

    const flush = () => {
      if (!buf) return;
      out += alive
        ? `<span style="white-space:pre-wrap;color:#4a9d6e">${this.escapeHtml(buf)}</span>`
        : `<span style="white-space:pre-wrap;color:#c25a5a;text-decoration:line-through">${this.escapeHtml(buf)}</span>`;
      buf = "";
    };

    for (const rec of records) {
      if (rec.c === "\n") continue;
      if (alive === null) alive = rec.alive;
      if (rec.alive !== alive) {
        flush();
        alive = rec.alive;
      }
      buf += rec.c;
    }
    flush();
    return out;
  }

  // ==================== 空闲停顿检测 ====================

  // ==================== 状态栏字数 ====================

  private updateStatusEditor() {
    this.statusEditor = this.app.workspace.getActiveViewOfType(MarkdownView)?.editor ?? null;
  }

  private scheduleStatusUpdate(delay = 150) {
    if (this.statusTimer !== null) clearTimeout(this.statusTimer);
    this.statusTimer = window.setTimeout(() => {
      this.statusTimer = null;
      this.renderStatusBar();
    }, delay);
  }

  private renderStatusBar() {
    const el = this.statusBarEl;
    if (!el) return;
    const editor = this.statusEditor;
    if (!this.trackerSettings.statusBar || !editor) {
      el.style.display = "none";
      el.textContent = "";
      return;
    }
    const selection = editor.getSelection();
    const n = selection ? countWords(selection) : countWords(editor.getValue());
    el.style.display = "";
    el.textContent = `${n}字`;
    el.title = `共 ${n} 字`;
  }


  private startIdleTimer() {
    if (this.idleTimer) return;
    this.idleTimer = window.setInterval(() => {
      const state = this.active;
      if (!state) return;
      const idleDuration = Date.now() - state.lastActiveTime;
      if (idleDuration >= this.idleThresholdMs && !state.idleRecorded) {
        state.pauses.push({ timestamp: Date.now(), duration: idleDuration });
        state.idleRecorded = true;
        this.scheduleSave();
        this.scheduleViewUpdate();
      }
      // 计时中时每秒重算时间与竞速数字
      if (this.session.running) this.updateAllViews();
    }, 1000);
  }

  // ==================== 视图刷新 ====================

  private scheduleViewUpdate() {
    if (this.viewTimer) return;
    this.viewTimer = window.setTimeout(() => {
      this.viewTimer = null;
      this.updateAllViews();
    }, VIEW_DEBOUNCE_MS);
  }

  private updateAllViews() {
    this.app.workspace.getLeavesOfType(VIEW_TYPE).forEach((leaf) => {
      if (leaf.view instanceof TrackerView) leaf.view.refreshAll();
    });
  }

  // ==================== 持久化 ====================

  private async loadPersisted() {
    let data: Partial<PersistedData> | null = null;
    try {
      data = (await this.loadData()) as Partial<PersistedData> | null;
    } catch {
      data = null;
    }
    if (!data) return;

    this.loadSettings(data);

    if (data.files) {
      for (const [path, raw] of Object.entries(data.files)) {
        if (!raw || !Array.isArray(raw.chars)) continue;
        const chars: CharRecord[] = raw.chars.map((row) => ({
          c: row[0],
          alive: row[1] === 1,
          input: row[2] === 1,
        }));
        this.fileStates.set(path, {
          chars,
          alive: chars.filter((rec) => rec.alive),
          current: chars.filter((rec) => rec.alive).map((rec) => rec.c).join(""),
          versions: (raw.versions ?? []).map((v) => ({ timestamp: v.t, content: v.c })),
          pauses: (raw.pauses ?? []).map((p) => ({ timestamp: p.t, duration: p.d })),
          totalInput: raw.totalInput ?? 0,
          totalDelete: raw.totalDelete ?? 0,
          lastActiveTime: Date.now(),
          idleRecorded: true,
          deleting: false,
        });
      }
    }

    // 修复历史数据里可能残留的编码字符
    for (const state of this.fileStates.values()) {
      state.chars = state.chars.filter((rec) => !/[A-Za-z]/.test(rec.c));
      state.alive = state.chars.filter((rec) => rec.alive);
      state.current = state.alive.map((rec) => rec.c).join("");
      if (state.versions.length === 0) {
        state.versions.push({ timestamp: Date.now(), content: state.current });
      }
    }
  }

  private loadSettings(data: Partial<PersistedData>) {
    const name = (data.settings?.name ?? "").trim();
    if (name) this.trackerSettings.rivalName = name;

    const speed = Number(data.settings?.speed);
    if (Number.isFinite(speed)) {
      this.trackerSettings.rivalSpeed = Math.min(
        MAX_RIVAL_SPEED,
        Math.max(MIN_RIVAL_SPEED, Math.round(speed)),
      );
    }

    if (data.settings?.sb !== undefined) {
      this.trackerSettings.statusBar = data.settings.sb !== 0;
    }
    if (data.settings?.hs !== undefined) {
      this.separatorHidden = data.settings.hs === 1;
    }


    const raw = data.session;
    if (!raw) return;
    const running = raw.r === 1;
    this.session = {
      running,
      startedAt: running ? Number(raw.s) || Date.now() : 0,
      elapsedMs: Math.max(0, Number(raw.e) || 0),
      baseInput: Math.max(0, Number(raw.bi) || 0),
      baseFinal: Math.max(0, Number(raw.bf) || 0),
    };
  }

  public getSettings(): TrackerSettings {
    return {
      rivalName: this.trackerSettings.rivalName,
      rivalSpeed: this.trackerSettings.rivalSpeed,
      statusBar: this.trackerSettings.statusBar,
    };
  }

  public updateSettings(patch: Partial<TrackerSettings>) {
    if (typeof patch.rivalName === "string") {
      this.trackerSettings.rivalName = patch.rivalName.trim() || DEFAULT_RIVAL_NAME;
    }
    if (typeof patch.rivalSpeed === "number" && Number.isFinite(patch.rivalSpeed)) {
      this.trackerSettings.rivalSpeed = Math.min(
        MAX_RIVAL_SPEED,
        Math.max(MIN_RIVAL_SPEED, Math.round(patch.rivalSpeed)),
      );
    }
    if (typeof patch.statusBar === "boolean") {
      this.trackerSettings.statusBar = patch.statusBar;
      this.scheduleStatusUpdate(0);
    }

    this.scheduleSave();
    this.updateAllViews();
  }

  private scheduleSave() {
    if (!this.loaded) return; // 加载阶段不要覆盖磁盘数据
    if (this.saveTimer) return;
    this.saveTimer = window.setTimeout(() => {
      this.saveTimer = null;
      void this.saveNow();
    }, SAVE_DEBOUNCE_MS);
  }

  private async saveNow() {
    const files: Record<string, PersistedFileState> = {};
    for (const [path, state] of this.fileStates) {
      files[path] = {
        chars: state.chars.map((rec) => [
          rec.c,
          rec.alive ? 1 : 0,
          rec.input ? 1 : 0,
        ]),
        versions: state.versions.map((v) => ({ t: v.timestamp, c: v.content })),
        pauses: state.pauses.map((p) => ({ t: p.timestamp, d: p.duration })),
        totalInput: state.totalInput,
        totalDelete: state.totalDelete,
      };
    }
    const payload: PersistedData = {
      version: 5,
      files,
      session: {
        r: this.session.running ? 1 : 0,
        s: this.session.startedAt,
        e: this.session.elapsedMs,
        bi: this.session.baseInput,
        bf: this.session.baseFinal,
      },
      settings: {
        name: this.trackerSettings.rivalName,
        speed: this.trackerSettings.rivalSpeed,
        sb: this.trackerSettings.statusBar ? 1 : 0,
        hs: this.separatorHidden ? 1 : 0,
      },
    };
    await this.saveData(payload);
  }

  // ==================== 重置（总览保留） ====================

  private resetState(state: FileState) {
    this.cancelDeleteSettle(state);

    // 总览也重置：以当前正文为新的基线
    state.chars = [...state.current].map((c) => ({
      c,
      alive: true,
      input: false,
    }));
    state.alive = [...state.chars];
    state.versions = [{ timestamp: Date.now(), content: state.current }];
    state.pauses = [];
    state.totalInput = 0;
    state.totalDelete = 0;
    state.lastActiveTime = Date.now();
    state.idleRecorded = false;
  }

  public resetTracker() {
    const state = this.active;
    if (!state) return;
    this.resetState(state);
    this.scheduleSave();
    this.scheduleViewUpdate();
  }


  onunload() {
    if (this.idleTimer) clearInterval(this.idleTimer);
    // 关闭前把“删除已结束但还没存档”的版本补上
    for (const state of this.deleteTimers.keys()) {
      state.deleting = false;
      this.pushVersion(state, state.current);
    }
    for (const timer of this.deleteTimers.values()) clearTimeout(timer);
    this.deleteTimers.clear();
    if (this.viewTimer) clearTimeout(this.viewTimer);
    if (this.statusTimer !== null) clearTimeout(this.statusTimer);
    if (this.saveTimer) clearTimeout(this.saveTimer);
    void this.saveNow();
  }
}

// ========== 侧边栏视图类 ==========
class TrackerView extends ItemView {
  private plugin: NovelWriteTrackerPlugin;
  private hideSep = false;
  constructor(leaf: WorkspaceLeaf, plugin: NovelWriteTrackerPlugin) {
    super(leaf);
    this.plugin = plugin;
  }

  getViewType() { return VIEW_TYPE; }
  getDisplayText() { return "写作删改追踪"; }
  getIcon() { return "pencil"; }

  async onOpen() {
    const container = this.containerEl.children[1] as HTMLElement;
    container.empty();
    container.addClass("novel-tracker-view");
    this.hideSep = this.plugin.isSeparatorHidden();

    container.createEl("div", { cls: "tracker-file", text: "" });

    // 顶部：与对手的同场竞速
    const duel = container.createDiv("duel-panel");
    const duelHead = duel.createDiv("duel-head");
    duelHead.createEl("span", { cls: "duel-name", text: "" });
    duelHead.createEl("span", { cls: "duel-tag", text: "对手" });
    const duelGrid = duel.createDiv("duel-grid");
    const rivalCol = duelGrid.createDiv("duel-col");
    rivalCol.createEl("div", { cls: "duel-score duel-rival", text: "0" });
    rivalCol.createEl("div", { cls: "duel-caption", text: "对手已写字数" });
    duelGrid.createEl("div", { cls: "duel-vs", text: "VS" });
    const ownCol = duelGrid.createDiv("duel-col duel-col-right");
    ownCol.createEl("div", { cls: "duel-score duel-own", text: "0" });
    ownCol.createEl("div", { cls: "duel-caption", text: "我的最终保留" });
    duel.createEl("div", { cls: "duel-delta", text: "" });

    // 统计区
    container.createEl("div", { text: "数据", cls: "section-title" });
    const statsGrid = container.createDiv("tracker-stats");
    this.createStatCard(statsGrid, "累计输入", "stat-input");
    this.createStatCard(statsGrid, "累计删除", "stat-delete");
    this.createStatCard(statsGrid, "最终保留", "stat-final");
    this.createStatCard(statsGrid, "留存率", "stat-retention");

    // 本次写作：计时与时速
    const sessionBlock = container.createDiv("session-block");
    const sessionHead = sessionBlock.createDiv("session-head");
    const timerBtn = sessionHead.createEl("button", {
      cls: "timer-btn",
      attr: { id: "timer-btn", "aria-label": "开始计时" },
    });
    setIcon(timerBtn, "play");
    timerBtn.addEventListener("click", () => void this.plugin.toggleSession());

    const timerMain = sessionHead.createDiv("timer-main");
    timerMain.createEl("div", { cls: "timer-text", text: "00:00:00", attr: { id: "timer-text" } });
    timerMain.createEl("div", { cls: "timer-caption", text: "本次写作计时" });
    sessionHead.createEl("div", { cls: "session-status", text: "未开始", attr: { id: "session-status" } });

    const speeds = sessionBlock.createDiv("speeds");
    const rawItem = speeds.createDiv("speed-item");
    rawItem.createEl("div", { cls: "speed-label", text: "原始时速" });
    const rawValue = rawItem.createDiv("speed-value");
    rawValue.createEl("span", { text: "0", attr: { id: "speed-raw" } });
    rawValue.createEl("small", { text: "字/时" });

    const actualItem = speeds.createDiv("speed-item");
    actualItem.createEl("div", { cls: "speed-label", text: "实际时速" });
    const actualValue = actualItem.createDiv("speed-value");
    actualValue.createEl("span", { text: "0", attr: { id: "speed-actual" } });
    actualValue.createEl("small", { text: "字/时" });

    const actions = container.createDiv("tracker-actions");
    const exportBtn = actions.createEl("button", {
      text: "导出 Markdown",
      cls: "tracker-btn",
    });
    exportBtn.addEventListener("click", () => void this.plugin.exportMarkdown());

    const resetBtn = actions.createEl("button", {
      text: "重置统计与总览",
      cls: "tracker-btn mod-warning",
    });
    resetBtn.addEventListener("click", () => this.plugin.resetTracker());
    // 整体删改总览
    const overviewHead = container.createDiv("overview-head");
    overviewHead.createEl("div", { text: "总览", cls: "section-title" });
    const eyeBtn = overviewHead.createEl("button", {
      cls: "overview-toggle",
      attr: { id: "overview-toggle", "aria-label": "隐藏 ··· 标记行" },
    });
    setIcon(eyeBtn, this.hideSep ? "eye-off" : "eye");
    eyeBtn.dataset.icon = this.hideSep ? "eye-off" : "eye";
    eyeBtn.addEventListener("click", () => {
      this.hideSep = !this.hideSep;
      this.plugin.setSeparatorHidden(this.hideSep);
      this.refreshAll();
    });
    const overviewCard = container.createDiv({
      cls: "overview-card",
      attr: { id: "overview-area" },
    });
    // 内容全部经 escapeHtml 转义，仅用于呈现已跟踪字符
    this.setRichHtml(overviewCard, this.plugin.getOverviewDiffHtml());

    // 版本演变
    container.createEl("div", { text: "版本", cls: "section-title" });
    const versionList = container.createDiv({ attr: { id: "version-list" } });
    this.setRichHtml(versionList, this.plugin.getVersionListHtml());
    // 使用说明
    const tip = container.createDiv("tracker-tip");
    const tipLines = [
      "· 用两行 ··· 包裹写作区域",
      "· 点击总览右上角眼睛，隐藏所有 ··· 标记行",
    ];
    tipLines.forEach((line, i) => {
      if (i > 0) tip.createEl("br");
      tip.appendText(line);
    });

    this.refreshAll();
  }

  private createStatCard(parent: HTMLElement, label: string, cls: string) {
    const card = parent.createDiv("stat-card");
    card.createDiv({ cls: `stat-number ${cls}`, text: "0" });
    card.createDiv({ cls: "stat-label", text: label });
  }

  public refreshAll() {
    const stats = this.plugin.calculateStats();
    const session = this.plugin.getSessionStats();
    const settings = this.plugin.getSettings();
    const fmt = (n: number) => Math.max(0, Math.round(n)).toLocaleString("zh-CN");
    const setText = (sel: string, text: string) => {
      const el = this.containerEl.querySelector(sel);
      if (el) el.textContent = text;
    };
    setText(".stat-input", String(stats.totalInput));
    setText(".stat-delete", String(stats.totalDelete));
    setText(".stat-final", String(stats.finalChars));
    setText(".stat-retention", `${stats.retentionRate}%`);
    setText(".tracker-file", `当前文件：${this.plugin.getActiveFileName()}`);

    // 对局
    setText(".duel-name", settings.rivalName);
    setText(".duel-tag", `设定时速 ${fmt(settings.rivalSpeed)} 字/时`);
    setText(".duel-rival", fmt(session.rivalChars));
    setText(".duel-own", fmt(session.ownChars));

    const delta = this.containerEl.querySelector(".duel-delta");
    if (delta) {
      delta.empty();
      if (!session.running && session.elapsedMs === 0) {
        delta.appendText(`点击开始，与 ${settings.rivalName} 同场竞速`);
      } else if (session.gap === 0) {
        delta.appendText(`您当前与 ${settings.rivalName} 持平`);
      } else {
        const ahead = session.gap > 0;
        delta.appendText("您当前已");
        delta.createSpan({
          cls: ahead ? "duel-ahead" : "duel-behind",
          text: ahead ? "反超" : "落后",
        });
        delta.appendText(` ${settings.rivalName} ${fmt(Math.abs(session.gap))} 字`);
      }
    }

    // 计时与时速
    setText("#timer-text", this.formatDuration(session.elapsedMs));
    setText("#speed-raw", fmt(session.rawRate));
    setText("#speed-actual", fmt(session.actualRate));
    let statusLabel = "未开始";
    if (session.running) statusLabel = "计时中";
    else if (session.elapsedMs > 0) statusLabel = "已停止";
    setText("#session-status", statusLabel);

    const timerBtn = this.containerEl.querySelector("#timer-btn");
    if (timerBtn instanceof HTMLElement) {
      const icon = session.running ? "square" : "play";
      if (timerBtn.dataset.icon !== icon) {
        timerBtn.empty();
        setIcon(timerBtn, icon);
        timerBtn.dataset.icon = icon;
      }
      timerBtn.setAttr("aria-label", session.running ? "停止计时" : "开始计时");
      timerBtn.toggleClass("is-running", session.running);
    }
    const eyeToggle = this.containerEl.querySelector("#overview-toggle");
    if (eyeToggle instanceof HTMLElement) {
      const icon = this.hideSep ? "eye-off" : "eye";
      if (eyeToggle.dataset.icon !== icon) {
        eyeToggle.empty();
        setIcon(eyeToggle, icon);
        eyeToggle.dataset.icon = icon;
      }
      eyeToggle.setAttr("aria-label", this.hideSep ? "显示 ··· 标记行" : "隐藏 ··· 标记行");
      eyeToggle.toggleClass("is-off", this.hideSep);
    }

    const overview = this.containerEl.querySelector("#overview-area");
    if (overview instanceof HTMLElement) {
      this.setRichHtml(overview, this.plugin.getOverviewDiffHtml());
    }
    const versionList = this.containerEl.querySelector("#version-list");
    if (versionList instanceof HTMLElement) {
      this.setRichHtml(versionList, this.plugin.getVersionListHtml());
    }
  }

  /** 只接受由本插件生成、已转义的 span 结构，避免直接写 innerHTML。 */
  private setRichHtml(target: HTMLElement, html: string) {
    const parsed = new DOMParser().parseFromString(html, "text/html");
    target.empty();
    while (parsed.body.firstChild) {
      target.append(parsed.body.firstChild);
    }
  }

  private formatDuration(ms: number): string {
    const total = Math.floor(Math.max(0, ms) / 1000);
    const h = Math.floor(total / 3600);
    const m = Math.floor((total % 3600) / 60);
    const s = total % 60;
    const p = (v: number) => String(v).padStart(2, "0");
    return `${p(h)}:${p(m)}:${p(s)}`;
  }

  async onClose() {}
}

// ========== 设置页 ==========
class TrackerSettingTab extends PluginSettingTab {
  private plugin: NovelWriteTrackerPlugin;

  constructor(app: App, plugin: NovelWriteTrackerPlugin) {
    super(app, plugin);
    this.plugin = plugin;
  }

  display() {
    const { containerEl } = this;
    containerEl.empty();
    containerEl.createEl("h2", { text: "写作删改追踪" });

    const settings = this.plugin.getSettings();

    new Setting(containerEl)
      .setName("对手昵称")
      .setDesc("显示在面板顶部的竞速对手名字")
      .addText((text) =>
        text
          .setPlaceholder(DEFAULT_RIVAL_NAME)
          .setValue(settings.rivalName)
          .onChange((value) => this.plugin.updateSettings({ rivalName: value })),
      );

    new Setting(containerEl)
      .setName("对手时速")
      .setDesc(`点击开始后，对手按此速度匀速增长（${MIN_RIVAL_SPEED}–${MAX_RIVAL_SPEED} 字/小时）`)
      .addText((text) => {
        text.inputEl.type = "number";
        text
          .setValue(String(settings.rivalSpeed))
          .onChange((value) => {
            const speed = Number(value);
            if (Number.isFinite(speed)) this.plugin.updateSettings({ rivalSpeed: speed });
          });
      });

    new Setting(containerEl)
      .setName("字数统计")
      .setDesc("以word的字数统计规则计算中文字数。")
      .addToggle((toggle) =>
        toggle
          .setValue(settings.statusBar)
          .onChange((value) => this.plugin.updateSettings({ statusBar: value })),
      );

  }
}

