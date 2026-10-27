
module

public import CFSG.LocalAnalysis.StandardType.GGReflExtE6Base

public import CFSG.LocalAnalysis.StandardType.GGReflExtFinal
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6AllDefs
public import Certificates.Certificate708604
public import Certificates.Data.CFSGNative.ReflExt.E6
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.ReflExt CFSG.TwoNodeSmall

theorem lr6E6All_of_certificate :
    LR6E6All :=
  Certificates.certificate708604

end CFSG.StandardType

end
