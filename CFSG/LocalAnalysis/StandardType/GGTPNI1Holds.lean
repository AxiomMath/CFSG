module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1A24
public import CFSG.LocalAnalysis.StandardType.GGTPNI1BCCore
public import CFSG.LocalAnalysis.StandardType.GGTPNI1TypeA

public section

namespace CFSG.StandardType

theorem ggI1OfPairL_holds
    : GGI1OfPairL :=
  ggI1OfPairL_of_rank
    (ggI1PairRank_of_pairs ggI1PairRankOn_A24 (tpbc_of_core tpbcCore_holds) ggI1PairRankOn_TypeA)

end CFSG.StandardType

end
