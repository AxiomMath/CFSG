module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosDefs

public section

namespace CFSG.StandardType

@[expose] def GGSixLieKnownRemainingPosNoPSL :
    Prop :=
  GGSixLieKnown .PSU ∧ GGSixLieKnown .PSp ∧ GGSixLieKnown .POmegaPlus ∧
    GGSixLieKnown .POmegaMinus ∧ GGSixLieKnownPos .F4 ∧ GGSixLieKnown .E6 ∧
    GGSixLieKnown .E7 ∧ GGSixLieKnown .E8 ∧ GGSixLieKnownPos .twistedE6

end CFSG.StandardType
