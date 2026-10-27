module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G]

theorem c23_binaryNatural_of_v1_eq_bot (M : Subgroup G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hv1 : v1Sub M ⊥ V hV L = ⊥)
    (h : BinaryNaturalSL (lStar M ⊥ V hV L) (wStar M ⊥ V hV L) ⊥ 3 1) :
    BinaryNaturalSL (barSub ⊥ V hV L) (wTil ⊥ V hV L) ⊥ 3 1 := by
  have hW : ∀ V₁ : Subgroup G, V₁ = ⊥ → BinaryNaturalSL (barSub V₁ V hV L)
      (imgTil V₁ V hV (wSub ⊥ V hV L)) ⊥ 3 1 →
      BinaryNaturalSL (barSub ⊥ V hV L) (wTil ⊥ V hV L) ⊥ 3 1 := by
    intro V₁ hV₁ h
    subst hV₁
    rwa [show imgTil ⊥ V hV (wSub ⊥ V hV L) = wTil ⊥ V hV L from imgTil_preTil ⊥ V hV _] at h
  exact hW _ hv1 h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
