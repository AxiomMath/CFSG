module

public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped commutatorElement

theorem commutator_le_center_of_isExtraspecialExpP
    {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q) :
    ⁅Q, Q⁆ ≤ (Subgroup.center ↥Q).map Q.subtype := by
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQ
  rw [← hQ.2.2.1, Subgroup.map_subtype_commutator]

theorem commutator_mem_center_of_isExtraspecialExpP
    {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    ⁅x, y⁆ ∈ (Subgroup.center ↥Q).map Q.subtype :=
  commutator_le_center_of_isExtraspecialExpP hQ
    (Subgroup.commutator_mem_commutator hx hy)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
