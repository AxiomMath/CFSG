module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosDefs

public section

namespace CFSG.StandardType

@[expose] def GGSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmegaMinus :
    Prop :=
  GGSixLieKnown .POmegaPlus ∧ GGSixLieKnownPos .E6 ∧ GGSixLieKnownPos .E7 ∧
    GGSixLieKnownPos .E8 ∧ GGSixLieKnownPos .twistedE6

end CFSG.StandardType
