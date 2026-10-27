
module

public import CFSG.LocalAnalysis.StandardType.GGReflNineFinalBase

public import CFSG.LocalAnalysis.StandardType.GGReflNineSound
public import CFSG.LocalAnalysis.StandardType.GGReflNineChart
public import CFSG.LocalAnalysis.StandardType.GGReflExtFinal
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineAllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepChart
public import Certificates.Certificate708606
public import Certificates.Data.CFSGNative.NineAll.Check

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.NineAll CFSG.TwoNodeSmall CFSG.ReflExt

theorem lr6NineAll_of_certificate :
    LR6NineAll :=
  Certificates.certificate708606

end CFSG.StandardType

end
