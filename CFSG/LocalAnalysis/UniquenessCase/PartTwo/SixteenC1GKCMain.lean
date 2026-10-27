module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem omegaKitC_holds : OmegaKitC := by
  intro W _ _ H h
  obtain ⟨β, hβ⟩ := natOmegaMinus_exists_model h
  exact ⟨s16c1c_formSing hβ, s16c1c_normIsom hβ, s16c1c_outerNons hβ, s16c1c_rankLe4 hβ,
    s16c1c_transPair hβ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
