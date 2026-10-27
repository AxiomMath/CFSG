module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflAssembly
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CSuppTwo
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflNorm
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflCoef
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSign
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflTrick
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflArith
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableFlip
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableSmall

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_refl_holds : C2ReflLeaf :=
  c2_refl_of_steps c2_suppTwo_holds c2_reflNorm_holds c2_reflCoef_holds c2_reflSign_holds
    c2_reflTrick_holds c2_reflArith_holds c2_tableFlip_holds c2_tableSmall_holds

end CFSG.StandardType.HdRo7C
