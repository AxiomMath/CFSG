module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs

public section

namespace CFSG.StandardType

@[expose] def GGD4OddCentKGInputsOffTablePRest : Prop :=
  GGD4OddCentInnerInput ∧ GGLieInnerDiagInput ∧ GGLieSU3FixedInput ∧ GGTwE6InnerDiagInput

end CFSG.StandardType
