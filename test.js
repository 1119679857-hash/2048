'use strict';
/*
 * Headless test suite for 2048/index.html
 *
 * The real game script is evaluated inside a minimal DOM stub, then driven by
 * synthetic key presses. Three phases:
 *   1. random play  - core invariants after every single move
 *   2. greedy play  - reaches deep boards, exercises big merges + undo
 *   3. win path     - WIN_VALUE patched to 16 to verify the win / keep-playing flow
 */

const fs = require('fs');
const path = require('path');

const HTML = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');
const SCRIPT = HTML.match(/<script>([\s\S]*?)<\/script>/)[1];

let FAILS = 0;
function check(cond, msg) {
  if (!cond) { console.log('  FAIL: ' + msg); FAILS++; }
}

/* ------------------------------------------------------------------ *
 * minimal DOM stub
 * ------------------------------------------------------------------ */
function makeEl(tag) {
  const el = {
    tagName: tag, children: [], parentNode: null, className: '',
    dataset: {}, textContent: '', offsetWidth: 0, clientWidth: 400,
    attrs: {}, handlers: {},
    style: { setProperty() {} },
    appendChild(c) { c.parentNode = el; el.children.push(c); return c; },
    removeChild(c) {
      const i = el.children.indexOf(c);
      if (i >= 0) el.children.splice(i, 1);
      c.parentNode = null;
      return c;
    },
    setAttribute(k, v) { el.attrs[k] = v; },
    getAttribute(k) { return el.attrs[k]; },
    addEventListener(t, fn) { (el.handlers[t] = el.handlers[t] || []).push(fn); },
    click() { (el.handlers.click || []).forEach(fn => fn({})); }
  };
  const set = new Set();
  el.classList = {
    add: (...c) => c.forEach(x => set.add(x)),
    remove: (...c) => c.forEach(x => set.delete(x)),
    contains: c => set.has(c),
    toggle: c => (set.has(c) ? set.delete(c) : set.add(c))
  };
  Object.defineProperty(el, 'innerHTML', {
    get() { return ''; },
    set() { el.children.forEach(c => (c.parentNode = null)); el.children = []; }
  });
  return el;
}

function seeded(seed) {
  let s = seed >>> 0;
  return function () {
    s = (s * 1664525 + 1013904223) >>> 0;
    return s / 4294967296;
  };
}

const IDS = ['board', 'tiles', 'score', 'best', 'scoreAdd', 'undo', 'overlay',
             'overlayMsg', 'overlaySub', 'overlayKeep', 'newGame', 'overlayRestart'];

/** Boot a fresh, isolated instance of the game. */
function bootstrap(seed, transform) {
  const reg = {};
  IDS.forEach(id => { reg[id] = makeEl('div'); });

  const keyHandlers = [];
  const documentStub = { getElementById: id => reg[id], createElement: makeEl };
  const windowStub = { addEventListener(t, fn) { if (t === 'keydown') keyHandlers.push(fn); } };
  const store = { _d: {}, getItem(k) { return this._d[k] === undefined ? null : this._d[k]; }, setItem(k, v) { this._d[k] = String(v); } };
  const MathStub = {};
  Object.getOwnPropertyNames(Math).forEach(k => { MathStub[k] = Math[k]; });
  MathStub.random = seeded(seed);

  let code = SCRIPT;
  if (transform) code = transform(code);
  new Function('document', 'window', 'localStorage', 'requestAnimationFrame', 'Math', code)(
    documentStub, windowStub, store, () => {}, MathStub
  );

  const tilesEl = reg.tiles;
  const overlayEl = reg.overlay;

  function press(key) { keyHandlers.forEach(fn => fn({ key, preventDefault() {} })); }

  /** Read the board out of the DOM (transforms -> grid coords). */
  function readBoard() {
    const items = [];
    for (const el of tilesEl.children) {
      if (el.style.zIndex === '1') continue;           // tile sliding out after a merge
      const inner = el.children[0];
      const m = /translate\(([-\d.]+)px,\s*([-\d.]+)px\)/.exec(el.style.transform || '');
      if (!m) { check(false, 'tile element without a transform'); continue; }
      items.push({ value: parseInt(inner.textContent, 10), px: parseFloat(m[1]), py: parseFloat(m[2]) });
    }
    const xs = [...new Set(items.map(t => t.px))].sort((a, b) => a - b);
    const ys = [...new Set(items.map(t => t.py))].sort((a, b) => a - b);
    const grid = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]];
    const seen = new Set();
    for (const t of items) {
      const gx = xs.indexOf(t.px), gy = ys.indexOf(t.py);
      if (gx < 0 || gy < 0) { check(false, 'tile outside the grid'); continue; }
      const key = gy + ',' + gx;
      if (seen.has(key)) { check(false, 'two tiles occupy cell ' + key); continue; }
      seen.add(key);
      grid[gy][gx] = t.value;
    }
    return { grid, count: items.length };
  }

  return {
    reg, press, readBoard, store, overlayEl,
    score: () => parseInt(reg.score.textContent, 10) || 0,
    overlayShown: () => overlayEl.classList.contains('show'),
    overlayKind: () => overlayEl.dataset.kind
  };
}

/* ------------------------------------------------------------------ *
 * shared board helpers
 * ------------------------------------------------------------------ */
const sum = g => g.flat().reduce((a, b) => a + b, 0);
const count = g => g.flat().filter(v => v > 0).length;
const isPow2 = v => v >= 2 && Number.isInteger(Math.log2(v));
const maxOf = g => Math.max(...g.flat());
function canMove(g) {
  if (g.flat().some(v => v === 0)) return true;
  for (let y = 0; y < 4; y++) for (let x = 0; x < 4; x++) {
    if (x < 3 && g[y][x] === g[y][x + 1]) return true;
    if (y < 3 && g[y][x] === g[y + 1][x]) return true;
  }
  return false;
}
function heuristic(g) {
  const flat = g.flat();
  const empties = flat.filter(v => !v).length;
  const maxV = maxOf(g);
  const cornerOk = Math.max(g[0][0], g[0][3], g[3][0], g[3][3]) === maxV ? 1 : 0;
  let mono = 0;
  for (let y = 0; y < 4; y++) for (let x = 0; x < 3; x++) {
    const a = Math.log2(g[y][x] || 1), b = Math.log2(g[y][x + 1] || 1);
    if (b > a) mono -= (b - a);
  }
  return empties * 1000 + cornerOk * 250 + mono * 5;
}

const DIRS = ['ArrowUp', 'ArrowRight', 'ArrowDown', 'ArrowLeft'];

/** One move + a full battery of invariants. Returns the new board. */
function stepAndVerify(game, prev, label) {
  const prevSum = sum(prev);
  const prevCount = count(prev);
  const prevScore = game.score();

  const before = game.readBoard().grid;
  check(sum(before) === prevSum, label + ': board drifted before the move');
  check(count(before) === prevCount, label + ': tile count drifted before the move');

  const dir = DIRS[Math.floor(Math.random() * 4)];
  game.press(dir);

  const b = game.readBoard();
  const g = b.grid;
  const afterSum = sum(g);

  for (const v of g.flat()) {
    if (v > 0) check(isPow2(v), label + ': illegal tile value ' + v);
  }
  check(b.count <= 16, label + ': more than 16 tiles');

  if (afterSum !== prevSum) {
    // effective move: exactly one new 2/4 tile was spawned, merges preserve the sum
    const delta = afterSum - prevSum;
    check(delta === 2 || delta === 4, label + ': effective move must add a 2 or 4, got +' + delta);

    const merges = prevCount + 1 - b.count;
    check(merges >= 0, label + ': negative merge count ' + merges);
    if (merges > 0) check(game.score() > prevScore, label + ': merge without a score increase');
    else check(game.score() === prevScore, label + ': score changed without a merge');
  } else {
    check(b.count === prevCount, label + ': no-op move changed the tile count');
    check(game.score() === prevScore, label + ': no-op move changed the score');
  }
  return g;
}

/* ------------------------------------------------------------------ *
 * phase 1 - random play
 * ------------------------------------------------------------------ */
console.log('phase 1: random play invariants');
{
  const game = bootstrap(20261007);
  const b0 = game.readBoard();
  check(b0.count === 2, 'new game starts with 2 tiles, got ' + b0.count);
  check([4, 6, 8].includes(sum(b0.grid)), 'initial sum sane: ' + sum(b0.grid));
  check(game.score() === 0, 'score starts at 0');
  check(!game.overlayShown(), 'no overlay at start');
  check(game.reg.undo.disabled === true, 'undo starts disabled');

  let prev = b0.grid, moves = 0, effective = 0;
  for (let i = 0; i < 5000; i++) {
    if (game.overlayShown()) {
      check(!canMove(prev), 'game over only when no move is possible');
      break;
    }
    const g = stepAndVerify(game, prev, 'random#' + i);
    if (sum(g) !== sum(prev)) effective++;
    prev = g; moves++;
  }
  console.log('  moves=' + moves + ' effective=' + effective +
              ' maxTile=' + maxOf(prev) + ' score=' + game.score());
}

/* ------------------------------------------------------------------ *
 * phase 2 - undo correctness + greedy play
 * ------------------------------------------------------------------ */
console.log('phase 2: undo + greedy play');
{
  const game = bootstrap(777);
  let prev = game.readBoard().grid;

  // deterministic undo check
  for (let i = 0; i < 12; i++) {
    const beforeBoard = prev, beforeScore = game.score(), beforeCount = count(prev);
    const g = stepAndVerify(game, prev, 'undo#' + i);
    if (sum(g) !== sum(beforeBoard)) {
      check(!game.reg.undo.disabled, 'undo should be enabled after a real move');
      game.press('z');
      const u = game.readBoard();
      check(sum(u.grid) === sum(beforeBoard), 'undo must restore the exact sum');
      check(count(u.grid) === beforeCount, 'undo must restore the tile count');
      check(game.score() === beforeScore, 'undo must restore the score');
      prev = u.grid;
      continue;
    }
    prev = g;
  }

  // greedy: probe every direction, then commit to the best one
  let best = 0, moves = 0, undoProbes = 0;
  for (let i = 0; i < 4000; i++) {
    if (game.overlayShown()) {
      check(!canMove(prev), 'greedy game over only when no move is possible');
      break;
    }
    const startBoard = game.readBoard().grid;
    const startSum = sum(startBoard);
    const options = [];

    for (const d of DIRS) {
      game.press(d);
      const after = game.readBoard();
      if (sum(after.grid) === startSum) continue;      // no-op, nothing to undo
      options.push({ d, h: heuristic(after.grid) });
      game.press('z');                                  // roll the probe back
      undoProbes++;
      const back = game.readBoard();
      check(sum(back.grid) === startSum, 'probe undo must restore the board');
    }

    if (!options.length) {                              // genuinely stuck
      check(!canMove(startBoard), 'stuck board must have no legal move');
      break;
    }

    options.sort((a, b) => b.h - a.h);
    const chosen = options[0].d;
    const beforeScore = game.score();
    const beforeCount = count(startBoard);
    game.press(chosen);
    moves++;

    const g = game.readBoard().grid;
    const afterSum = sum(g);
    for (const v of g.flat()) if (v > 0) check(isPow2(v), 'greedy: illegal value ' + v);
    check(afterSum - startSum === 2 || afterSum - startSum === 4,
          'greedy: effective move must add a 2 or 4, got +' + (afterSum - startSum));
    if (afterSum !== startSum) {
      const merges = beforeCount + 1 - count(g);
      if (merges > 0) check(game.score() > beforeScore, 'greedy: merge without a score increase');
    }
    prev = g;
    best = Math.max(best, maxOf(g));
  }
  console.log('  moves=' + moves + ' probes undone=' + undoProbes +
              ' maxTile=' + best + ' score=' + game.score());
  check(best >= 64, 'greedy play should reach at least a 64 tile, got ' + best);
}

/* ------------------------------------------------------------------ *
 * phase 3 - win / keep playing flow
 * ------------------------------------------------------------------ */
console.log('phase 3: win flow (WIN_VALUE patched to 16)');
{
  const game = bootstrap(31337, code => code.replace('var WIN_VALUE = 2048;', 'var WIN_VALUE = 16;'));
  let prev = game.readBoard().grid;
  let won = false;

  for (let i = 0; i < 3000; i++) {
    if (game.overlayShown()) {
      check(game.overlayKind() === 'win', 'expected the win overlay, got ' + game.overlayKind());
      check(game.reg.overlayKeep.style.display !== 'none', 'win overlay must offer 继续挑战');
      won = true;
      break;
    }
    const g = stepAndVerify(game, prev, 'win#' + i);
    prev = g;
  }

  check(won, 'a 16 tile should have been reached and triggered the win overlay');
  if (won) {
    check(game.reg.overlayKeep.style.display === '', 'keep-playing button should be visible on win');
    check(maxOf(prev) >= 16, 'win overlay only after reaching the target tile');

    // moving while the win overlay is open must be blocked
    const frozen = sum(game.readBoard().grid);
    game.press('ArrowLeft');
    game.press('ArrowDown');
    check(sum(game.readBoard().grid) === frozen, 'moves must be blocked while the win overlay is open');

    // 继续挑战 resumes the game
    game.reg.overlayKeep.click();
    check(!game.overlayShown(), 'clicking 继续挑战 must close the overlay');
    const before = sum(game.readBoard().grid);
    let resumed = false;
    for (const d of DIRS) {
      game.press(d);
      if (sum(game.readBoard().grid) !== before) { resumed = true; break; }
    }
    check(resumed, 'the game must resume after 继续挑战');
    prev = game.readBoard().grid;

    // the win overlay must not pop up again
    let again = false;
    for (let i = 0; i < 400; i++) {
      if (game.overlayShown()) { again = game.overlayKind() === 'win'; break; }
      const g = stepAndVerify(game, prev, 'post-win#' + i);
      prev = g;
    }
    check(!again, 'the win overlay must not trigger a second time');
    console.log('  maxTile after continuing: ' + maxOf(prev) + ' score=' + game.score());
  }
}

/* ------------------------------------------------------------------ */
console.log('\n' + (FAILS === 0 ? 'ALL CHECKS PASSED' : FAILS + ' CHECK(S) FAILED'));
process.exit(FAILS === 0 ? 0 : 1);
