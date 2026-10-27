module

import CFSG.LieType.SpecialLinear.SLModel.PairModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Label
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Label

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.SLModel

theorem six_le_finrank_range_sub_one_of_pair {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 4) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K) W)
    [ρ.IsIrreducible] {ε : Fin 2 → Finset (Fin 4)} (hε : HasTwistedLabel ρ ε)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) K))
      ρ.asModule) = 2)
    {j : Fin 4} (hj : (j : ℕ) = 1 ∨ (j : ℕ) = 3) (h0 : ε 0 = {j}) (h1 : ε 1 = {j})
    {y : Matrix.SpecialLinearGroup (Fin 4) K} (hy : y * y = 1) (hy1 : y ≠ 1) :
    6 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  obtain ⟨k, hfield, hcharp, hEalg, hKalg, y₀, χ, J, h0', ht, hχ, hJ, β, hβ⟩ := hε
  letI : Field k := hfield
  letI : CharP k 2 := hcharp
  letI : Algebra (Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin 4) K)) ρ.asModule) k := hEalg
  letI : Algebra K k := hKalg
  have hE' : Nat.card (Module.End (MonoidAlgebra (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin 4) K)) ρ.asModule) = 2 ^ 1 := by
    simpa using hE
  have hrank :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.finrank_range_sub_one_eq_mul
      (s := 1) ρ hE' k y
  have hrankβ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.finrank_range_sub_one_eq_of_equiv
      (τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ))
      (τ' := slModelRep (F := K) (k := k) (m := 3) ε) β hβ y
  have hpair := two_mul_le_finrank_range_slModelRep_pair (m := 3) (f := 2) (k := k)
    (by norm_num) ε (r₁ := 0) (r₂ := 1) (by decide) hj h0 h1
    (by intro r hr0 hr1; fin_cases r <;> simp_all) hy hy1
  rw [hrank, hrankβ]
  omega

end CFSG.LocalAnalysis.WeakClosure81
