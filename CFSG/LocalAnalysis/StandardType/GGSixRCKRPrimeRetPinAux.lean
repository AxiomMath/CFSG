module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetIota
public import CFSG.LieType.Chevalley.RootCommutator

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

open Classical in
theorem rckPn_pinnedX_commutator
    {τ : Tag} {K : Type} [Field K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a) (hb : IsRoot τ b) (hne : a + b ≠ 0) (c d : K) :
    ⁅pinnedX τ K a c, pinnedX τ K b d⁆ =
      if IsRoot τ (a + b) then pinnedX τ K (a + b) (c * d) else 1 := by
  by_cases hr : IsRoot τ (a + b)
  · rw [if_pos hr]
    have hneab : a ≠ b := by
      intro hab
      subst hab
      have h2 : IsRoot τ (2 • a) := by simpa [two_smul] using hr
      have h1 := eq_one_of_isRoot_nsmul h2
      omega
    have hne' : a ≠ -b := fun h => hne (by rw [h, neg_add_cancel])
    obtain ⟨hC, hF⟩ :=
      (simply_laced_root_commutator_unit τ (Or.inr hτ) ha hb hneab hne').1 hr
    rw [hF K c d]
    have h1 : ((commConst τ a b (1, 1) : ℤ) : K) = 1 := by
      rcases hC with h | h <;> rw [h] <;> simp [CharTwo.neg_eq]
    rw [h1, one_mul]
  · rw [if_neg hr, commutatorElement_eq_one_iff_commute]
    by_cases hab : a = b
    · subst hab
      rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
    · have hne' : a ≠ -b := fun h => hne (by rw [h, neg_add_cancel])
      exact (simply_laced_root_commutator_unit τ (Or.inr hτ) ha hb hab hne').2 hr K
        _ (Subgroup.subset_closure ⟨c, rfl⟩) _ (Subgroup.subset_closure ⟨d, rfl⟩)

end CFSG.StandardType.RCKRP

end
