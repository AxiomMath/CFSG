module

public import CFSG.Quasithin.Background.F918U0
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

public section

namespace CFSG.Quasithin.D35Chk

open scoped Matrix

@[expose] def bm (a : Nat) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  fun i j => if a.testBit (5 * (i : ℕ) + (j : ℕ)) then 1 else 0

@[expose] def upI (p : ℕ) : Fin 5 := Fin.ofNat 5 (upos.getD p 0 / 5)

@[expose] def upJ (p : ℕ) : Fin 5 := Fin.ofNat 5 (upos.getD p 0 % 5)

@[expose] def codeOfMat (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) : ℕ :=
  (List.range 10).foldr (fun p acc => 2 * acc + (A (upI p) (upJ p)).val) 0

@[expose] def colSum (col : Nat → Nat) (c : Nat) : Nat :=
  (List.range 10).foldl (fun acc p => Nat.xor acc (Nat.mul (bit c p) (col p))) 0

@[expose] def upSum (c : Nat) : Nat := colSum upE c

@[expose] def altSum (c : Nat) : Nat := colSum altE c

@[expose] def IsSub (S : Nat) : Prop :=
  S < 2 ^ 1024 ∧ ∀ c d, S.testBit c = true → S.testBit d = true → S.testBit (c ^^^ d) = true

end CFSG.Quasithin.D35Chk
