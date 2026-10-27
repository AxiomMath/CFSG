
module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepFinalBase

public import CFSG.LocalAnalysis.StandardType.GGReflDepSound
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepChart
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepAllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepExclusion
public import Certificates.Certificate708607

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.DepFrame CFSG.NineAll CFSG.TwoNodeSmall CFSG.ReflExt

theorem lr6A5DepAll_of_certificate :
    LR6A5DepAll :=
  Certificates.certificate708607

end CFSG.StandardType

end
