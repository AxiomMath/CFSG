
module

public import CFSG.LocalAnalysis.StandardType.GGReflExtA5Base

public import CFSG.LocalAnalysis.StandardType.GGReflExtFinal
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5AllDefs
public import Certificates.Certificate708605
public import Certificates.Data.CFSGNative.ReflExt.A5
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.ReflExt CFSG.TwoNodeSmall

theorem lr6A5All_of_certificate :
    LR6A5All :=
  Certificates.certificate708605

end CFSG.StandardType

end
