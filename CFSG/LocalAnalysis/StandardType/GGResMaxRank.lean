module

public import CFSG.LocalAnalysis.StandardType.GGResMaxRankModel
public import CFSG.LocalAnalysis.StandardType.GGResMaxRankCases

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResMaxRankInput_of_inputs
    (hM : GGResMaxRankModelInput) (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) : GGResMaxRankInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases (hM G p B Bs x L D J y K hH hP).cases with hI | hII
  · exact ggMaxRank_caseI_weyl hKG hOrb hFix hFixK hH hI
  · exact (ggMaxRank_caseII_false hFixK hH hII).elim

end CFSG.StandardType

end
