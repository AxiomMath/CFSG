module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs

public section

namespace CFSG.StandardType

@[expose] def GGD4OddCentKGInputsOffTablePRestNoLTStrong : Prop :=
  GGD4OddCentInnerInput ∧ GGLieInnerDiagInput ∧ GGTwE6InnerDiagInput

end CFSG.StandardType
