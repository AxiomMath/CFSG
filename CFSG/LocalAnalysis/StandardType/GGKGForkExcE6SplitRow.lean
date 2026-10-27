module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitSylow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggKGExcInputSplit_E6
    :
    GGKGExcInputSplit .E6 6 :=
  fun _ _ _ _ _ hp hp5 hpq => ExcE6Split.excSCTorusInput_E6_split hp hp5 hpq

end CFSG.StandardType

end
