module

public import CFSG.Monster.B.Dyadic.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native CFSG.Monster.B.Binary.Native CFSG.KC.BM.Lat
open scoped Matrix

@[expose] def Fact3101 : Prop :=
  (∀ g : Fin 26, fvec ᵥ* Cmat g = fvec)
    ∧ (∀ y : Fin 4371 → ZMod 2, (∀ g : Fin 26, y ᵥ* Cmat g = y) → y = 0 ∨ y = fvec)
    ∧ (∀ x : Fin 4371 → ZMod 2, (∀ g : Fin 26, Cmat g *ᵥ x = x) → x = 0)
    ∧ (Qmat 0 - 1).rank = 1860
    ∧ (Qmat 25 - 1).rank = 2862
    ∧ Qmat 0 * Qmat 0 = 1
    ∧ Qmat 25 * Qmat 25 * Qmat 25 = 1

@[expose] def Fact3102 : Prop :=
  (∀ i : Fin 4371, diagExpK[(i : ℕ)]! ≤ 7)
    ∧ (∀ i : Fin 4371, Bz i i = 2 ^ diagExpK[(i : ℕ)]!)
    ∧ (∀ i k : Fin 4371, k < i → Bz i k = 0)
    ∧ (∀ i k : Fin 4371, i < k → Bz i k < 128)
    ∧ (∀ i : Fin 4371, ∃ c : Fin 4371 → ℤ, ∀ k : Fin 4371,
        ∑ t : Fin 4371, c t * Bz t k = if k = i then 128 else 0)

@[expose] def Fact3103 : Prop :=
  ((List.range 8).map (expCountOf diagExpK) = [0, 12, 284, 993, 1782, 1035, 243, 22] ∧
      expDefectOf diagExpK = 13123)
    ∧ (fixedVector.testBit 1197 = true ∧ ∀ i < 1197, fixedVector.testBit i = false)

@[expose] def Fact3106 : Prop := ∀ (g : Fin 26) (i t : Fin 4371), (Cnum g i t).den = 1

end CFSG.Monster.B.Dyadic

end
