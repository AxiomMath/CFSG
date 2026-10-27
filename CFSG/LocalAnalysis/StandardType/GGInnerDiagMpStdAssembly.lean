module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitary
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdTwE6

public section

namespace CFSG.StandardType

section Families

theorem ggInnerDiagMpInput_holds : GGInnerDiagMpInput :=
  ggInnerDiagMpInput_of_std ggInnerDiagStdUnitary_holds ggInnerDiagStdE6_holds
    ggInnerDiagStdTwE6_holds

end Families

end CFSG.StandardType
