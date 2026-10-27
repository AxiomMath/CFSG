module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3FrameSplit
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem l3ThreeNoFive_holds : L3ThreeNoFive := by
  intro X _ _ hX h5
  have : Finite (MulAut X) :=
    Finite.of_injective (fun α : MulAut X => (α : X → X)) DFunLike.coe_injective
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have key : ∀ (τ : CFSG.Open.StatedLieTag), (τ = .PSL ∨ τ = .PSU) →
      CFSG.Open.StatedClassicalModel X τ 3 3 1 →
      ¬ 5 ∣ 1 * CFSG.RankThree.OuterOrder.determinantParameter τ 3 (3 ^ 1) →
      5 ∣ Nat.card X := fun τ hτ hT hd => by
    obtain ⟨x, hx⟩ := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      hτ le_rfl Nat.prime_three le_rfl hT).2 α hα hd
    have h1 : 5 ∣ orderOf x := by
      rw [← hα, ← hx]
      exact orderOf_map_dvd _ x
    exact h1.trans (orderOf_dvd_natCard x)
  rcases hX with hL | hU
  · have hT := hL.statedClassicalModel (by decide)
    have h := key .PSL (Or.inl rfl) hT (by decide)
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three hT] at h
    norm_num at h
  · have hT := hU.statedClassicalModel (by decide)
    have h := key .PSU (Or.inr rfl) hT (by decide)
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hT] at h
    norm_num at h

end CFSG.LocalAnalysis.UniquenessCase.UC22
