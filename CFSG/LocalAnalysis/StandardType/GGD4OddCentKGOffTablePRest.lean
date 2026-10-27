module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKGOffTablePRestDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentGraphCore
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeDefs

public section

namespace CFSG.StandardType

theorem ggD4OddCentKGInputsOffTableP_of_rest
    (h : GGD4OddCentKGInputsOffTablePRest) :
    GGD4OddCentKGInputsOffTableP :=
  ⟨ggD4OddCentGraphInput_holds, h⟩

end CFSG.StandardType
