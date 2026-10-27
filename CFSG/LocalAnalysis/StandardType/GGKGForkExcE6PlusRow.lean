module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6PlusSylow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggKGExcInputNonsplit_E6 :
    GGKGExcInputNonsplit .E6 4 :=
  fun _ _ _ _ _ hp hp5 hpq => ExcE6Plus.excSCTorusInput_E6_plus hp hp5 hpq

end CFSG.StandardType

end
