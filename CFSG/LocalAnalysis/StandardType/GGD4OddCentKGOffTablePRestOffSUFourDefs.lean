module

public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOn

public section

namespace CFSG.StandardType

@[expose] def GGD4OddCentKGInputsOffTablePRestOffSUFour : Prop :=
  GGD4OddCentInnerInput ∧ GGLieInnerDiagInput ∧
    GGLieSU3FixedInputOn (fun lab => ¬ GGLabelSUFour lab) ∧ GGTwE6InnerDiagInput

end CFSG.StandardType
