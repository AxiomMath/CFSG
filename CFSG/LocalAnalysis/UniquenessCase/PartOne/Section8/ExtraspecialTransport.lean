module

public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem isExtraspecialExpP_of_mulEquiv
    {Q R : Type} [Group Q] [Group R] (e : Q ≃* R)
    (h : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 R) :
    CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 Q := by
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at h ⊢
  obtain ⟨hcard, hexp, hcomm, hcenter⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact hcard
  · rw [Monoid.exponent_eq_of_mulEquiv e]
    exact hexp
  · have hmap : (commutator Q).map (e : Q →* R) = commutator R := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_equiv_top]
    have hcenter_map : (Subgroup.center Q).map (e : Q →* R) = Subgroup.center R :=
      Subgroup.map_center_eq e
    exact Subgroup.map_injective e.injective (by rw [hmap, hcenter_map, hcomm])
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hcenter

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
