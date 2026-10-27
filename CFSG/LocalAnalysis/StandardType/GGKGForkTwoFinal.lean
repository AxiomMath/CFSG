module

public import CFSG.LocalAnalysis.StandardType.GGKGForkTwoRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE7Nons
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE8Nons
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcF4Nons
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6SplitRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Row
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitOddE
public import CFSG.LocalAnalysis.StandardType.GGKGForkSmallTwo

public section

namespace CFSG.StandardType

theorem ggForkLatticeKGInput_holds
    : GGForkLatticeKGInput :=
  ggForkLatticeKGInput_of_open ggKGExcInputSplit_E6 ggKGExcInputNonsplit_E7 ggKGExcInputNonsplit_E8
    ggKGExcInputNonsplit_F4 ggKGTwE6InputSplit_four ggKGTwE6InputNonsplit_five
    ggKGTwoOn_unitarySplitOdd ggKGTwoOn_small

end CFSG.StandardType

end
