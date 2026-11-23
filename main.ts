// Tiny stack VM (ISA.md): one switch over opcode bytes; trap checks in ISA.md's order.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';

const OUT_MAX = 65536;

// Per opcode: [immediate bytes, pops, pushes]; unlisted bytes are unknown opcodes.
const T: Record<number, number[]> = {
  0: [0, 0, 0], 1: [1, 0, 1], 2: [4, 0, 1], 3: [0, 1, 0], 4: [0, 1, 2], 5: [0, 2, 2], 6: [0, 2, 3], 7: [0, 3, 3],
  0x17: [0, 1, 1], 0x1b: [0, 1, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0], 0x32: [2, 1, 0], 0x33: [2, 0, 0],
  0x34: [0, 0, 0], 0x40: [0, 1, 1], 0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1], 0x53: [0, 1, 0],
};
for (let o = 0x10; o <= 0x1e; o++) T[o] ??= [0, 2, 1]; // binary ops (0x1f unused)
for (let o = 0x20; o <= 0x22; o++) T[o] = [0, 2, 1];
const IMM = new Int8Array(256).fill(-1), POPS = new Uint8Array(256), PUSHES = new Uint8Array(256);
for (const k in T) { IMM[k] = T[k][0]; POPS[k] = T[k][1]; PUSHES[k] = T[k][2]; }

// Runs one program; returns [output bytes, exit code].
function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const n = p.length;
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(OUT_MAX);
  let sp = 0, cs = 0, ol = 0, ip = 0, pc = 0, steps = 0; // data sp, call sp, out len, in pos
  const fin = (code: number): [Uint8Array, number] => [out.slice(0, ol), code];
  for (;;) {
    if (steps === 1000000) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = p[pc], imm = IMM[op];
    if (imm < 0) return fin(5);
    if (pc + imm >= n) return fin(9); // immediate cut off
    steps++;
    const nx = pc + 1 + imm; // next instruction
    const left = sp - POPS[op];
    if (left < 0) return fin(2);
    if (left + PUSHES[op] > 256) return fin(3);
    pc = nx;
    switch (op) {
      case 0: return fin(0);
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: { // JMP/JZ/JNZ: signed offset from next
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + (((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16);
        break;
      }
      case 0x33: // CALL: unsigned target
        if (cs === 64) return fin(7);
        C[cs++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 0x34:
        if (cs === 0) return fin(8);
        pc = C[--cs]; break;
      case 0x40: { const a = D[sp - 1]; if (a < 0 || a > 255) return fin(6); D[sp - 1] = M[a]; break; } // LOAD
      case 0x41: { const a = D[sp - 1]; if (a < 0 || a > 255) return fin(6); M[a] = D[sp - 2]; sp -= 2; break; } // STORE
      case 0x50: { // PRINT: decimal ASCII, all or nothing
        const s = String(D[sp - 1]);
        if (ol + s.length > OUT_MAX) return fin(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC
        if (ol >= OUT_MAX) return fin(11);
        out[ol++] = D[--sp] & 255; break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN
      case 0x53: return fin(D[--sp] & 255); // EXIT
      default: { // binary ( a b -- r )
        const b = D[sp - 1], a = D[sp - 2];
        let r = 0;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: case 0x14: case 0x15: case 0x16:
            if (b === 0) return fin(4);
            if (op === 0x13) r = a === -2147483648 && b === -1 ? a : (a / b) | 0; // DIV
            else if (op === 0x14) r = b === -1 ? 0 : (a % b) | 0; // MOD
            else if (op === 0x15) r = Math.floor((a >>> 0) / (b >>> 0)) | 0; // DIVU
            else r = ((a >>> 0) % (b >>> 0)) | 0; // MODU
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // shifts: low 5 bits of b
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = a >>> 0 < b >>> 0 ? 1 : 0; break;
        }
        sp--; D[sp - 1] = r;
      }
    }
  }
}

// Answer each instance: stdout.bin and exit.txt.
for (const id of readdirSync('/input').sort()) {
  const [o, c] = run(readFileSync(`/input/${id}/program.bin`), readFileSync(`/input/${id}/input.bin`));
  mkdirSync(`/output/${id}`, { recursive: true });
  writeFileSync(`/output/${id}/stdout.bin`, o);
  writeFileSync(`/output/${id}/exit.txt`, c + '\n');
}
