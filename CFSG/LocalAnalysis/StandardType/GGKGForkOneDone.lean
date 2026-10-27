module

public import CFSG.LocalAnalysis.StandardType.GGKGForkOneRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcSplitL0
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Row
public import CFSG.LocalAnalysis.StandardType.GGKGForkSmallRow

public section

namespace CFSG.StandardType

theorem ggForkRootSL2KGInput_holds
    : GGForkRootSL2KGInput :=
  ggForkRootSL2KGInput_of_rest ggKGExcInputSplit_E6 ggKGExcInputSplit_E7 ggKGExcInputSplit_E8
    ggKGExcInputSplit_F4 ggKGTwE6InputNonsplit_five ggKGOneOn_small

end CFSG.StandardType

end
