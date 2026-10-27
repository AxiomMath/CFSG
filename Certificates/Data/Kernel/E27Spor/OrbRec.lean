module

public import Certificates.Data.Kernel.E27Lie.Defs
public import CFSG.Monster.B.Pinned.Primes.ThreeAction
public import Mathlib

public section

namespace CFSG.KC.E27Spor

open CFSG.KC.Enum CFSG.Monster.B.Pinned

@[expose] def decD : ℕ → ℕ → List ℕ
  | 0, _ => []
  | d + 1, c => c % 3 :: decD d (c / 3)

@[expose] noncomputable def orbTreeC (d : ℕ) (rows : List (List (List ℕ))) (C pp pj : ℕ → ℕ)
    (b i : ℕ) : Bool :=
  bAnd(Nat.blt (C i) (Nat.pow 3 d), bIf(Nat.beq i 0, Nat.beq (C 0) b,
    bAnd(Nat.blt (pp i) i, bAnd(Nat.blt (pj i) rows.length,
      Nat.beq (C i) (lcode (lvecMul 3 d (decD d (C (pp i))) (rows.getD (pj i) [])))))))

@[expose] noncomputable def orbImgC (d : ℕ) (rows : List (List (List ℕ))) (C : ℕ → ℕ)
    (im : ℕ → ℕ → ℕ) (N i : ℕ) : Bool :=
  allN rows.length fun t => bAnd(Nat.blt (im t i) N,
    Nat.beq (C (im t i)) (lcode (lvecMul 3 d (decD d (C i)) (rows.getD t []))))

end CFSG.KC.E27Spor

end
