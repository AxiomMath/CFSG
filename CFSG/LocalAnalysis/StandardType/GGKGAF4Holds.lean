module

public import CFSG.LocalAnalysis.StandardType.GGKGAF4Core
public import CFSG.HardMathSupport.S2MathAs1.I1486.Complete

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace KGA

theorem ggF4C3CentInputStrong_holds :
    GGF4C3CentInputStrong :=
  ggF4C3CentInputStrong_of_core CFSG.HardMathSupport.S2MathAs1.I1486.ggF4CoreInput_holds

end KGA

end CFSG.StandardType

end
