module

public import CFSG.Quasithin.Recognition.CertF8
public import Mathlib

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin

@[expose] def validB (A : Array ℕ) : Bool := A.size == 16 && (List.range 16).all fun i => A[i]! < 8

@[expose] def idCode : Array ℕ :=
  Array.ofFn (n := 16) fun t => if t.val / 4 = t.val % 4 then 1 else 0

@[expose] def mulEntry (A B : Array ℕ) (i j : ℕ) : ℕ :=
  GF8.mulNat A[4 * i]! B[j]! ^^^ GF8.mulNat A[4 * i + 1]! B[4 + j]! ^^^
    GF8.mulNat A[4 * i + 2]! B[8 + j]! ^^^ GF8.mulNat A[4 * i + 3]! B[12 + j]!

@[expose] def mulCode (A B : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 16) fun t => mulEntry A B (t.val / 4) (t.val % 4)

@[expose] def frobCode (A : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 16) fun t => GF8.mulNat A[t.val]! A[t.val]!

@[expose] def frobPow : ℕ → Array ℕ → Array ℕ
  | 0, A => A
  | n + 1, A => frobCode (frobPow n A)

structure Pc where
  m : Array ℕ
  j : ℕ
deriving DecidableEq, Inhabited

@[expose] def mulP (p q : Pc) : Pc := ⟨mulCode p.m (frobPow p.j q.m), (p.j + q.j) % 3⟩

@[expose] def oneP : Pc := ⟨idCode, 0⟩

@[expose] def powP (p : Pc) : ℕ → Pc
  | 0 => oneP
  | n + 1 => mulP (powP p n) p

end CFSG.AGLEmbedding.KFactProofs.Sp48
