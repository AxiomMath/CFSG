module

public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem isPGroup_of_isExtraspecialExpP
    {G : Type} [Group G] {Q : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q) :
    IsPGroup 3 Q := by
  have hQdef := hQ
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQdef
  obtain ⟨hQcard, -, -, -⟩ := hQdef
  refine IsPGroup.of_card (n := 3) ?_
  rw [hQcard]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
