module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcE
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcF4
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOm
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSUOuter
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSpEight

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Tags

theorem ggRootCentSummandStructInput_holds : GGRootCentSummandStructInput :=
  ggRootCentSummandStructInput_of_excTags ggUFiveTwoRankInput_holds ggSpSixEightRankInput_holds
    ggRootCentDerivedTag_F4 ggRootCentDerivedTag_E6 ggRootCentDerivedTag_E7
    ggRootCentDerivedTag_E8 ggRootCentDerivedTag_twistedE6

end Tags

end CFSG.StandardType
