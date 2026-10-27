module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Holds
public import CFSG.LocalAnalysis.StandardType.ZS.DThree
public import CFSG.LocalAnalysis.StandardType.ZS.DLargeMain

public section

namespace CFSG.StandardType.ZS

theorem useInput_holds :
    UseInput :=
  useInput_of_cases DimThree.dimThreeCase_holds
    family_of_primitive_of_orderOf_mul_le_three dLargeCase_holds

end CFSG.StandardType.ZS

end
