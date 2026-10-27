module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs

public section

namespace CFSG.StandardType

@[expose] def GGD4OddCentKGInputsOpen : Prop :=
  GGD4OddCentGraphInput ∧ GGD4OddCentInnerInput ∧
    GGStdSubNotTriD4Input ∧ GGStdSubNotA1Input ∧ GGStdSubTwA2ScalarInput ∧
    GGStdSubTwA2CentreInput ∧ GGStdSubD4Input ∧ GGLieInnerDiagInput ∧ GGLieSU3FixedInput ∧
    GGTwE6InnerDiagInput

end CFSG.StandardType
