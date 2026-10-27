module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankE7
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankE8
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankE6
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankTwE6

public section

namespace CFSG.StandardType

theorem ggOrdPFieldConjAt_E6 :
    GGOrdPFieldConjAt .E6 :=
  ggOrdPFieldConjAt_of_centRank ggExcFieldAutCentRank_E6

theorem ggOrdPFieldConjAt_twistedE6
    (hThree : GGExcFieldAutCentRankTwE6Three) :
    GGOrdPFieldConjAt .twistedE6 :=
  ggOrdPFieldConjAt_of_centRank (ggExcFieldAutCentRank_twistedE6 hThree)

end CFSG.StandardType
