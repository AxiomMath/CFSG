module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankHolds

public section

namespace CFSG.StandardType

@[expose] def GGD4OddCentKGInputsRest : Prop :=
  GGD4OddCentGraphInput ∧ GGD4OddCentFieldInput ∧ GGD4OddCentInnerInput ∧
    GGStdSubNotTriD4Input ∧ GGStdSubNotA1Input ∧ GGStdSubTwA2ScalarInput ∧
    GGStdSubTwA2CentreInput ∧ GGStdSubD4Input ∧ GGLieInnerDiagInput ∧ GGLieSU3FixedInput ∧
    GGTwE6InnerDiagInput


theorem ggD4OddCentKGInputs_of_rest (h : GGD4OddCentKGInputsRest) : GGD4OddCentKGInputs :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2,
    ggTwE6ThreeRankInput_holds⟩

end CFSG.StandardType
