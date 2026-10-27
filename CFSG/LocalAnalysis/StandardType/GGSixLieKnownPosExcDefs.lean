module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2F4Pos

public section

namespace CFSG.StandardType

@[expose] def GGSixLieKnownRemainingPosExc :
    Prop :=
  GGSixLieKnown .PSU ∧ GGSixLieKnown .PSp ∧ GGSixLieKnown .POmegaPlus ∧
    GGSixLieKnown .POmegaMinus ∧ LieKnownR2.F4.GGSixF4PosExplicit ∧ GGSixLieKnownPos .E6 ∧
    GGSixLieKnownPos .E7 ∧ GGSixLieKnownPos .E8 ∧ GGSixLieKnownPos .twistedE6

end CFSG.StandardType
