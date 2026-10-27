module

public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem normal_subgroupOf_inf_of_normal
    {G : Type} [Group G] {L M P : Subgroup G}
    (hLM : L ≤ M) (hLnorm : (L.subgroupOf M).Normal) (hP : P ≤ M) :
    ((L ⊓ P).subgroupOf P).Normal := by
  haveI : (L.subgroupOf M).Normal := hLnorm
  have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A' := L) (A := M) P
  rwa [inf_eq_right.mpr hP] at h

theorem center_card_three_of_isExtraspecialExpP
    {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q) :
    Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3 := by
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQ
  rw [Subgroup.card_map_of_injective (K := Subgroup.center ↥Q) Q.subtype_injective]
  exact hQ.2.2.2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
