module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosDefs

public section

namespace CFSG.StandardType

@[expose] def GGSixLieKnownRemainingPosExcNoF4NoPSUPSp :
    Prop :=
  GGSixLieKnown .POmegaPlus ∧ GGSixLieKnown .POmegaMinus ∧ GGSixLieKnownPos .E6 ∧
    GGSixLieKnownPos .E7 ∧ GGSixLieKnownPos .E8 ∧ GGSixLieKnownPos .twistedE6

end CFSG.StandardType
