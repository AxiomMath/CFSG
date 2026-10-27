module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKGOffTablePRestNoLTStrongDefs
public import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagMain
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7Main

public section

namespace CFSG.StandardType

theorem ggD4OddCentKGInputsOffTablePRestNoLTStrong_of_inner
    (h : GGD4OddCentInnerInput) :
    GGD4OddCentKGInputsOffTablePRestNoLTStrong :=
  ⟨h, SCFourCover.ggLieInnerDiagInput_holds, ggTwE6InnerDiagInput_holds⟩

end CFSG.StandardType
