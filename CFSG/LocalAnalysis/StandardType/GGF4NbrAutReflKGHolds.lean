module

public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce

public section

namespace CFSG.StandardType

theorem ggF4NbrAutReflKGInput_holds :
    GGF4NbrAutReflKGInput :=
  ggF4NbrAutReflKGInput_of_adjoint fun _ _ _ _ _ hp hp2 _ hE hcard =>
    ggAutomizer_adjointF4_of_card hp hp2 hE hcard

theorem ggF4NbrAutReflXiKGInput_holds :
    GGF4NbrAutReflXiKGInput :=
  ggF4NbrAutReflXiKGInput_of_refl ggF4NbrAutReflKGInput_holds

end CFSG.StandardType
