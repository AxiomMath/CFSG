module

public import CFSG.GroupTheory.McBrideGomiStatement
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.FusionAsc10
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.GroupTheory Subgroup

theorem familyControlsFusion_calMOf_of_charNormalizers {G : Type} [Group G] [Finite G]
    (D : Data G) (h : FamilyControlsFusion (charNormalizers D.T) D.T) :
    FamilyControlsFusion (calMOf D.T) D.T := by
  refine FamilyControlsFusion.of_le_mem h ?_
  rintro H ⟨C, hC, hCT, hchar, rfl⟩
  have hTN : D.T ≤ normalizer (C : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hCT).mp inferInstance
  have hloc : IsTwoLocal (normalizer (C : Set G)) :=
    ⟨C, hC, D.sylowG.isPGroup.to_le hCT, rfl⟩
  obtain ⟨N, hN, hHN⟩ := exists_maxTwoLocal_le_of_isTwoLocal hloc
  exact ⟨N, ⟨hN, hTN.trans hHN⟩, hHN⟩

theorem fusion_of_mcBrideGomi (h : McBrideGomi) {G : Type} [Group G] [Finite G] (D : Data G)
    (h640 : ∀ N : Subgroup G, rankThreeIsMaxTwoLocal N → ∀ L : Subgroup ↥N,
      ¬ CFSG.RankThree.PartOne.IsBlockInX L) :
    FamilyControlsFusion (calMOf D.T) D.T := by
  refine familyControlsFusion_calMOf_of_charNormalizers D
    (h G D.standing.simple D.standing.kProper D.standing.charTwo (fun N hN B hB => ?_) D.T
      D.sylowG)
  have hchar : CFSG.IsCharacteristicP 2 ↥N :=
    CFSG.QuasithinUnique.charTwo_iff_internal.mp (D.standing.charTwo N hN.1)
  exact h640 N hN B (hB.isBlockInX hchar)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
