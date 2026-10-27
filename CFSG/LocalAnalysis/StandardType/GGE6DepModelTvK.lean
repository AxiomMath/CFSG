module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

set_option autoImplicit false

namespace CFSG.StandardType.E6Dep.TvK

open CFSG.StandardType.E6Dep

theorem isTv6_of (a b : Vec6) (g : Mat6) (hg : g = 1 + Matrix.vecMulVec a b)
    (hba : b ⬝ᵥ a = 0) (ha : a ≠ 0)
    (hc : Fintype.card {v : Vec6 // b ⬝ᵥ v = 0} * 3 = 3 ^ 6) : IsTv6 g := by
  have hmv : ∀ v : Vec6, g.mulVec v = v + (b ⬝ᵥ v) • a := by
    intro v
    rw [hg, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  have hz : ∀ x y : ZMod 3, x * y = 0 → x = 0 ∨ y = 0 := by decide
  refine ⟨?_, ?_⟩
  · rw [← hc]
    congr 1
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [hmv, add_eq_left]
    refine ⟨fun h => ?_, fun h => by rw [h, zero_smul]⟩
    by_contra hne
    apply ha
    funext j
    have hj := congrFun h j
    rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
    exact (hz _ _ hj).resolve_left hne
  · intro v
    rw [hmv v, add_sub_cancel_left, hmv, dotProduct_smul, hba, smul_zero, zero_smul,
      add_zero]

end CFSG.StandardType.E6Dep.TvK

end
