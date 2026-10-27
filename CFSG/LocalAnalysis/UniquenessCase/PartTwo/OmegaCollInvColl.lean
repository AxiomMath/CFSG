module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem IsOmegaColl.isInvColl_top {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (h : IsOmegaColl Ω) : CFSG.Quasithin.E1.IsInvColl (⊤ : Subgroup G) Ω where
  le _ _ := le_top
  isElemAbelian := h.elemAbelian
  conj A hA t _ := by
    have h1 := h.conj A hA t⁻¹
    rwa [CFSG.Quasithin.conjSubgroup_eq_conjSub, inv_inv] at h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
