module

public import CFSG.HardMathSupport.GuralnickMalle.InvolutionRank

public section

namespace CFSG.RepresentationTheory

open Module
open scoped TensorProduct

theorem four_le_finrank_range_tensor_sub_one
    {K E X : Type*} [Field K] [CharP K 2]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (hE : Module.finrank K E = 4)
    (hX : Module.finrank K X = 3)
    (T : E →ₗ[K] E) (hT : T.comp T = 1)
    (S : X →ₗ[K] X) (hS : S.comp S = 1)
    (hTmove : T ≠ 1 → Module.finrank K (LinearMap.range (T - 1)) = 2)
    (hne : TensorProduct.map T S ≠ 1) :
    4 ≤ Module.finrank K (LinearMap.range (TensorProduct.map T S - 1)) := by
  classical
  have hmain := CFSG.HardMathSupport.GuralnickMalle.finrank_range_tensor_sub_one_add_ge
    (K := K) (V := E) (W := X) T hT S hS
  rw [hE, hX] at hmain
  by_cases hT1 : T = 1
  · have hTmove0 : Module.finrank K (LinearMap.range (T - 1)) = 0 := by
      rw [hT1]
      simp
    have hSne : S ≠ 1 := by
      intro hS1
      exact hne (by rw [hT1, hS1]; exact TensorProduct.map_one)
    have hSmove : 1 ≤ Module.finrank K (LinearMap.range (S - 1)) := by
      by_contra hlt
      have hzero : Module.finrank K (LinearMap.range (S - 1)) = 0 := by omega
      have hbot : LinearMap.range (S - 1) = ⊥ := Submodule.finrank_eq_zero.mp hzero
      have hsub : S - 1 = 0 := LinearMap.range_eq_bot.mp hbot
      exact hSne (sub_eq_zero.mp hsub)
    rw [hTmove0] at hmain
    omega
  · have hTmove2 : Module.finrank K (LinearMap.range (T - 1)) = 2 := hTmove hT1
    rw [hTmove2] at hmain
    omega

end CFSG.RepresentationTheory
