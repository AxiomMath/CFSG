module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKGOffTablePRestNoLTStrongDefs
public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOffSUFour
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKGOffTablePRestOffSUFourDefs

public section

namespace CFSG.StandardType

theorem ggD4OddCentKGInputsOffTablePRestOffSUFour_of_noLTStrong
    (h : GGD4OddCentKGInputsOffTablePRestNoLTStrong) :
    GGD4OddCentKGInputsOffTablePRestOffSUFour :=
  ⟨h.1, h.2.1, ggLieSU3FixedInputOn_offSUFour, h.2.2⟩

end CFSG.StandardType
