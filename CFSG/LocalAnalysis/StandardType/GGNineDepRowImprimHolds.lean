module

public import CFSG.LocalAnalysis.StandardType.GGNineDepRowImprim
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoImprim

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggNineDepRowImprim_holds : GGNineDepRowImprimInput :=
  fun _ _ _ _ _ _ _ _ _ X himp => ggLargeDep_noImprim X.case.lin X.case.two X.hA X.restr himp

end CFSG.StandardType

end
