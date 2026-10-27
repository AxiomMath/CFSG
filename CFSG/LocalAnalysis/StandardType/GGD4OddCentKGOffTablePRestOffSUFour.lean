module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKGOffTablePRestOffSUFourDefs
public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedSUFour
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKGOffTablePRestDefs

public section

namespace CFSG.StandardType

theorem ggD4OddCentKGInputsOffTablePRest_of_offSUFour
    (h : GGD4OddCentKGInputsOffTablePRestOffSUFour) : GGD4OddCentKGInputsOffTablePRest :=
  ⟨h.1, h.2.1, ggLieSU3FixedInput_of_split GGLabelSUFour ggLieSU3FixedInputOn_suFour h.2.2.1,
    h.2.2.2⟩

end CFSG.StandardType
