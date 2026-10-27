module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphK

public section

namespace CFSG.StandardType

theorem ggQ2_gammaNbrInL_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h1b : GGQTwoNoTwoNodeIndInput) (h5 : GGQTwoCentralizerInput)
    (hnode : GGQ2TwoNodeInput) (hdet : GGQ2GammaNbrDetAt GGQ2PosInL)
    (hpos : GGQ2GammaNbrPosAt GGQ2PosInL) : GGQ2GammaNbrInLInput :=
  fun hS hp hI1 hxL _ hu =>
    ggQ2_gammaNbr_core GGQ2PosInL hLB hP h1b h5 hnode
      (ggQ2_gammaNbrGraph_core GGQ2PosInL hLB hP h1b h5 hnode) hdet hpos hS hp hI1 hxL hu

end CFSG.StandardType

end
