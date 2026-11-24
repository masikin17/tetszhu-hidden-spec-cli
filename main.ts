// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does sections 1 to 4, 9 and 10 of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write. The other three formats are
// detected and then read as holding no edit, so they answer `error: parse 1`: reading unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7) and V4A patches (section 8), and matching lines at three tiers (section 5), are
// yours to write. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file as lines: its line break, its lines, and whether it ends with a break (SPEC.md section 3). */
interface FileDoc {
  br: string;
  lines: string[];
  finalBreak: boolean;
}
function parseFile(text: string): FileDoc {
  if (text === '') return { br: '\n', lines: [], finalBreak: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) parts.pop();
  return { br, lines: parts, finalBreak };
}
function renderFile(doc: FileDoc): string {
  if (doc.lines.length === 0) return '';
  return doc.lines.join(doc.br) + (doc.finalBreak ? doc.br : '');
}
const stripLead = (s: string): string => s.replace(/^[ \t]+/, '');
const stripTrail = (s: string): string => s.replace(/[ \t]+$/, '');
const stripBoth = (s: string): string => stripTrail(stripLead(s));
const leadingWs = (s: string): string => /^[ \t]*/.exec(s)?.[0] ?? '';
const onlyWs = (s: string): boolean => /^[ \t]*$/.test(s);

/** Line equality at a matching tier (SPEC.md section 5). */
function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return stripTrail(a) === stripTrail(b);
  return stripBoth(a) === stripBoth(b);
}
/** 0-based positions where O occurs in the file's lines at a tier, from `from` on. May overlap. */
function occurrences(fileLines: string[], O: string[], tier: number, from = 0): number[] {
  const out: number[] = [];
  if (O.length === 0) return out;
  for (let i = from; i + O.length <= fileLines.length; i++) {
    let ok = true;
    for (let j = 0; j < O.length; j++) {
      if (!lineEq(fileLines[i + j]!, O[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}
/** First tier at which O occurs at least once (from `from` on), or -1. With strict, tier 0 only. */
function findTier(fileLines: string[], O: string[], strict: boolean, from = 0): number {
  const maxTier = strict ? 0 : 2;
  for (let t = 0; t <= maxTier; t++) {
    if (occurrences(fileLines, O, t, from).length > 0) return t;
  }
  return -1;
}
/** One line of N: a context line (written as the file's own matched line) or a new line. */
interface NLine {
  text: string;
  ctxOffset: number | null;
}
/** Re-indent one new line at tier 2 (SPEC.md section 5): P is O's first line's leading whitespace, F the file's. */
function reindent(text: string, p: string, f: string): string {
  if (text === '' || onlyWs(text)) return text;
  if (p !== '' && !text.startsWith(p)) return text;
  return f + text.slice(p.length);
}
/** Replace O's lines at `pos` with N, re-indenting at tier 2. Context lines take the file's own line. */
function replaceAt(doc: FileDoc, pos: number, O: string[], N: NLine[], tier: number): void {
  const f = leadingWs(doc.lines[pos] ?? '');
  const p = leadingWs(O[0] ?? '');
  const out: string[] = [];
  for (const nl of N) {
    if (nl.ctxOffset !== null) out.push(doc.lines[pos + nl.ctxOffset]!);
    else if (tier === 2) out.push(reindent(nl.text, p, f));
    else out.push(nl.text);
  }
  doc.lines.splice(pos, O.length, ...out);
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

/** A rename recorded by an edit that moved a file (SPEC.md section 2). */
interface Move {
  from: string;
  to: string;
}
type Edit = (tree: Tree) => { move: Move } | void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/** One body line of a unified hunk or a V4A chunk. */
interface BodyLine {
  kind: 'ctx' | 'old' | 'new' | 'slash';
  text: string;
}
/** O and N built from a body, with N's context lines pointing at their offset in O. */
function onFromBody(body: BodyLine[]): { O: string[]; N: NLine[] } {
  const O: string[] = [];
  const N: NLine[] = [];
  for (const b of body) {
    if (b.kind === 'ctx') {
      N.push({ text: b.text, ctxOffset: O.length });
      O.push(b.text);
    } else if (b.kind === 'old') O.push(b.text);
    else if (b.kind === 'new') N.push({ text: b.text, ctxOffset: null });
  }
  return { O, N };
}
/** Whether a `\` line follows the body's last context or `+` line (SPEC.md section 6). */
function noEolAfterLast(body: BodyLine[]): boolean {
  let last = -1;
  for (let i = 0; i < body.length; i++) {
    if (body[i]!.kind === 'ctx' || body[i]!.kind === 'new') last = i;
  }
  if (last < 0) return false;
  return body[last + 1]?.kind === 'slash';
}

/** A unified-diff hunk (SPEC.md section 6). */
interface Hunk {
  a: number;
  body: BodyLine[];
}
/** A unified-diff section: one edit. Paths resolve ---/+++ over rename over diff --git. */
interface Section {
  oldPath: string | null;
  newPath: string | null;
  hasDash: boolean;
  isCreate: boolean;
  isDelete: boolean;
  hunks: Hunk[];
}
const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
function headerPath(raw: string): string | null {
  const t = raw.split('\t')[0]!.trim();
  if (t === '/dev/null') return null;
  return t.replace(/^a\//, '').replace(/^b\//, '');
}
function diffGitPaths(line: string): [string, string] | null {
  const m = /^diff --git a\/(\S+) b\/(\S+)\s*$/.exec(line);
  if (m === null) return null;
  return [m[1]!, m[2]!];
}

/** Parse a unified diff into sections (SPEC.md section 6). Throws Exit2 on a parse fault. */
function parseUnified(lines: string[]): Section[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let inHeader = false;
  let i = 0;
  const startSection = (oldP: string | null, newP: string | null, dash: boolean): Section => {
    const s: Section = { oldPath: oldP, newPath: newP, hasDash: dash, isCreate: false, isDelete: false, hunks: [] };
    sections.push(s);
    return s;
  };
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const paths = diffGitPaths(line);
      if (paths === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = startSection(paths[0], paths[1], false);
      inHeader = true;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (inHeader && cur !== null) {
        // A ---/+++ pair inside a header: it names this section's paths.
        cur.oldPath = headerPath(line.slice(4));
        cur.newPath = headerPath(lines[i + 1]!.slice(4));
        cur.hasDash = true;
        i += 2;
        continue;
      }
      cur = startSection(headerPath(line.slice(4)), headerPath(lines[i + 1]!.slice(4)), true);
      inHeader = true;
      i += 2;
      continue;
    }
    if (line.startsWith('--- ') && cur !== null && inHeader) {
      throw new Exit2(`error: parse ${i + 2}`);
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = HUNK_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      inHeader = false;
      const hunk: Hunk = { a: Number(m[1]), body: [] };
      cur.hunks.push(hunk);
      i++;
      // Body: lines starting with ' ', '-', '+', '\', or empty. Ends at the first other line,
      // at a diff --git line, at a --- line followed by +++, or at the end of the patch.
      while (i < lines.length) {
        const b = lines[i]!;
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (b === '') {
          hunk.body.push({ kind: 'ctx', text: '' });
          i++;
        } else if (b[0] === ' ') {
          hunk.body.push({ kind: 'ctx', text: b.slice(1) });
          i++;
        } else if (b[0] === '-') {
          hunk.body.push({ kind: 'old', text: b.slice(1) });
          i++;
        } else if (b[0] === '+') {
          hunk.body.push({ kind: 'new', text: b.slice(1) });
          i++;
        } else if (b[0] === '\\') {
          hunk.body.push({ kind: 'slash', text: b.slice(1) });
          i++;
        } else break;
      }
      // Empty lines at the end of a body are not part of it.
      while (hunk.body.length > 0) {
        const last = hunk.body[hunk.body.length - 1]!;
        if (last.kind === 'ctx' && last.text === '') hunk.body.pop();
        else break;
      }
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('rename from ')) {
        if (!cur.hasDash) cur.oldPath = line.slice('rename from '.length).trim();
      } else if (line.startsWith('rename to ')) {
        if (!cur.hasDash) cur.newPath = line.slice('rename to '.length).trim();
      } else if (line.startsWith('new file mode')) cur.isCreate = true;
      else if (line.startsWith('deleted file mode')) cur.isDelete = true;
      // index, old/new mode, similarity/dissimilarity index, Index: and any other line are ignored.
      i++;
      continue;
    }
    // Outside bodies and headers, lines are ignored (prose, code fences).
    i++;
  }
  return sections;
}

/** Apply one section's hunks to a file's lines, returning the new lines and final break. */
function applyHunks(doc: FileDoc, hunks: Hunk[], strict: boolean, path: string): FileDoc {
  const out: FileDoc = { br: doc.br, lines: [...doc.lines], finalBreak: doc.finalBreak };
  let d = 0;
  for (const hunk of hunks) {
    const { O, N } = onFromBody(hunk.body);
    if (O.length === 0) {
      const beforeLen = out.lines.length;
      const at = Math.min(hunk.a + d, beforeLen);
      out.lines.splice(at, 0, ...N.map((n) => n.text));
      if (at === beforeLen) out.finalBreak = !noEolAfterLast(hunk.body);
      d += N.length;
      continue;
    }
    const tier = findTier(out.lines, O, strict);
    if (tier < 0) throw new Fail('no-match', path);
    const occ = occurrences(out.lines, O, tier);
    const target = hunk.a - 1 + d;
    let best = occ[0]!;
    let bestDist = Math.abs(best - target);
    for (const p of occ) {
      const dist = Math.abs(p - target);
      if (dist < bestDist) {
        best = p;
        bestDist = dist;
      }
    }
    const runsToEnd = best + O.length === out.lines.length;
    replaceAt(out, best, O, N, tier);
    if (runsToEnd) out.finalBreak = !noEolAfterLast(hunk.body);
    d += N.length - O.length;
  }
  return out;
}

/** One unified section as an edit (SPEC.md section 6). */
function unifiedSectionEdit(sec: Section, strict: boolean): Edit {
  return (tree) => {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    if (sec.isCreate || oldP === null) {
      if (newP === null) return;
      if (!safe(newP)) throw new Fail('unsafe', newP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const plus: string[] = [];
      let noEol = false;
      for (const h of sec.hunks) {
        for (let bi = 0; bi < h.body.length; bi++) {
          const b = h.body[bi]!;
          if (b.kind === 'new') {
            plus.push(b.text);
            // The last + line overall decides: a \ line right after it means no final break.
            noEol = h.body[bi + 1]?.kind === 'slash';
          }
        }
      }
      tree.now.set(newP, plus.length === 0 ? '' : plus.join('\n') + (noEol ? '' : '\n'));
      return;
    }
    if (sec.isDelete || newP === null) {
      if (!safe(oldP)) throw new Fail('unsafe', oldP);
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    if (oldP !== newP) {
      if (!safe(oldP)) throw new Fail('unsafe', oldP);
      if (!safe(newP)) throw new Fail('unsafe', newP);
      const before = tree.get(oldP);
      if (before === null) throw new Fail('missing', oldP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const doc = applyHunks(parseFile(before), sec.hunks, strict, oldP);
      tree.now.set(newP, renderFile(doc));
      tree.now.set(oldP, null);
      return { move: { from: oldP, to: newP } };
    }
    if (!safe(oldP)) throw new Fail('unsafe', oldP);
    const before = tree.get(oldP);
    if (before === null) throw new Fail('missing', oldP);
    const doc = applyHunks(parseFile(before), sec.hunks, strict, oldP);
    tree.now.set(oldP, renderFile(doc));
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  return parseUnified(lines).map((s) => unifiedSectionEdit(s, strict));
}

/** One SEARCH/REPLACE block as an edit (SPEC.md section 7). */
function searchReplaceEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const doc = parseFile(before);
    const tier = findTier(doc.lines, oldLines, strict);
    if (tier < 0) throw new Fail('no-match', path);
    const occ = occurrences(doc.lines, oldLines, tier);
    if (occ.length > 1) throw new Fail('ambiguous', path);
    const N: NLine[] = newLines.map((t) => ({ text: t, ctxOffset: null }));
    replaceAt(doc, occ[0]!, oldLines, N, tier);
    tree.now.set(path, renderFile(doc));
  };
}

/** Parse SEARCH/REPLACE blocks (SPEC.md section 7). Throws Exit2 on a parse fault. */
function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevReplaceEnd = -1;
  let prevPath: string | null = null;
  const nextSearch = (from: number): number => {
    for (let j = from; j < lines.length; j++) if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') return j;
    return lines.length;
  };
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLine = i;
    const bound = nextSearch(searchLine + 1);
    let eq = -1;
    for (let j = searchLine + 1; j < bound; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < bound; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    let path: string | null = null;
    for (let j = searchLine - 1; j > prevReplaceEnd; j--) {
      const t = lines[j]!;
      if (blank(t)) continue;
      if (t.trim().startsWith('```')) continue;
      path = t.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    edits.push(searchReplaceEdit(path, lines.slice(searchLine + 1, eq), lines.slice(eq + 1, rep), strict));
    prevPath = path;
    prevReplaceEnd = rep;
    i = rep + 1;
  }
  return edits;
}

/** One V4A chunk. */
interface Chunk {
  anchor: string | null;
  body: BodyLine[];
  eof: boolean;
}
function v4aAddEdit(path: string, fileLines: string[]): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) !== null) throw new Fail('exists', path);
    tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
  };
}
function v4aDeleteEdit(path: string): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) === null) throw new Fail('missing', path);
    tree.now.set(path, null);
  };
}
function v4aUpdateEdit(path: string, moveTo: string | null, chunks: Chunk[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const doc = parseFile(before);
    let cursor = 0;
    for (const chunk of chunks) {
      if (chunk.anchor !== null) {
        const atier = findTier(doc.lines, [chunk.anchor], strict, cursor);
        if (atier < 0) throw new Fail('no-match', path);
        const aocc = occurrences(doc.lines, [chunk.anchor], atier, cursor);
        cursor = aocc[0]! + 1;
      }
      const { O, N } = onFromBody(chunk.body);
      if (O.length === 0) {
        const at = chunk.eof ? doc.lines.length : cursor;
        doc.lines.splice(at, 0, ...N.map((n) => n.text));
        cursor = at + N.length;
        continue;
      }
      const tier = findTier(doc.lines, O, strict, cursor);
      if (tier < 0) throw new Fail('no-match', path);
      const occ = occurrences(doc.lines, O, tier, cursor);
      let pos: number;
      if (chunk.eof) {
        const endPos = doc.lines.length - O.length;
        if (endPos < cursor || !occ.includes(endPos)) throw new Fail('no-match', path);
        pos = endPos;
      } else {
        pos = occ[0]!;
      }
      replaceAt(doc, pos, O, N, tier);
      cursor = pos + N.length;
    }
    const out = renderFile(doc);
    if (moveTo !== null) {
      tree.now.set(moveTo, out);
      tree.now.set(path, null);
      return { move: { from: path, to: moveTo } };
    }
    tree.now.set(path, out);
  };
}

/** Parse a V4A patch (SPEC.md section 8). Throws Exit2 on a parse fault. */
function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const isHeader = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    if (!isHeader(line)) throw new Exit2(`error: parse ${i + 1}`);
    if (line.startsWith('*** Add File: ')) {
      const path = line.slice('*** Add File: '.length).trim();
      i++;
      const rawIdx: number[] = [];
      while (i < last && !isHeader(lines[i]!)) {
        rawIdx.push(i);
        i++;
      }
      while (rawIdx.length > 0 && blank(lines[rawIdx[rawIdx.length - 1]!]!)) rawIdx.pop();
      const fileLines: string[] = [];
      for (const idx of rawIdx) {
        const l = lines[idx]!;
        if (l === '') fileLines.push('');
        else if (l.startsWith('+')) fileLines.push(l.slice(1));
        else throw new Exit2(`error: parse ${idx + 1}`);
      }
      edits.push(v4aAddEdit(path, fileLines));
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const path = line.slice('*** Delete File: '.length).trim();
      i++;
      const rawIdx: number[] = [];
      while (i < last && !isHeader(lines[i]!)) {
        rawIdx.push(i);
        i++;
      }
      while (rawIdx.length > 0 && blank(lines[rawIdx[rawIdx.length - 1]!]!)) rawIdx.pop();
      for (const idx of rawIdx) {
        if (!blank(lines[idx]!)) throw new Exit2(`error: parse ${idx + 1}`);
      }
      edits.push(v4aDeleteEdit(path));
      continue;
    }
    const updateLine = i;
    const path = line.slice('*** Update File: '.length).trim();
    i++;
    const rawIdx: number[] = [];
    while (i < last && !isHeader(lines[i]!)) {
      rawIdx.push(i);
      i++;
    }
    while (rawIdx.length > 0 && blank(lines[rawIdx[rawIdx.length - 1]!]!)) rawIdx.pop();
    let moveTo: string | null = null;
    let k = 0;
    if (k < rawIdx.length && lines[rawIdx[k]!]!.startsWith('*** Move to: ')) {
      moveTo = lines[rawIdx[k]!]!.slice('*** Move to: '.length).trim();
      k++;
    }
    const chunks: Chunk[] = [];
    let firstChunk = true;
    while (k < rawIdx.length) {
      const idx = rawIdx[k]!;
      const l = lines[idx]!;
      let anchor: string | null = null;
      if (l.startsWith('@@')) {
        anchor = l.slice(2).trim();
        if (anchor === '') anchor = null;
        k++;
      } else if (!firstChunk) {
        throw new Exit2(`error: parse ${idx + 1}`);
      }
      const body: BodyLine[] = [];
      let eof = false;
      while (k < rawIdx.length) {
        const bi = rawIdx[k]!;
        const bl = lines[bi]!;
        if (bl.startsWith('@@')) break;
        if (bl.trimEnd() === '*** End of File') {
          eof = true;
          k++;
          break;
        }
        if (bl === '') {
          body.push({ kind: 'ctx', text: '' });
          k++;
        } else if (bl[0] === ' ') {
          body.push({ kind: 'ctx', text: bl.slice(1) });
          k++;
        } else if (bl[0] === '-') {
          body.push({ kind: 'old', text: bl.slice(1) });
          k++;
        } else if (bl[0] === '+') {
          body.push({ kind: 'new', text: bl.slice(1) });
          k++;
        } else throw new Exit2(`error: parse ${bi + 1}`);
      }
      chunks.push({ anchor, body, eof });
      firstChunk = false;
    }
    if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLine + 1}`);
    edits.push(v4aUpdateEdit(path, moveTo, chunks, strict));
  }
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? searchReplaceEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  const moves: Move[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      const result = edit(tree);
      if (result !== undefined && result !== null) moves.push(result.move);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // A qualifying move replaces its D/A pair with one R line, sorted by the new path.
  const movedFrom = new Set<string>();
  const movedTo = new Set<string>();
  const qualifying: Move[] = [];
  for (const mv of moves) {
    if (tree.original(mv.from) !== null && tree.now.get(mv.from) === null && tree.original(mv.to) === null && tree.now.get(mv.to) !== null) {
      qualifying.push(mv);
      movedFrom.add(mv.from);
      movedTo.add(mv.to);
    }
  }
  const outRows: { key: string; text: string }[] = [];
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (movedFrom.has(p) || movedTo.has(p)) continue;
    outRows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const mv of qualifying) outRows.push({ key: mv.to, text: `R ${mv.from} -> ${mv.to}` });
  outRows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const rows = outRows.map((r) => r.text);
  if (!check) {
    for (const p of tree.now.keys()) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
