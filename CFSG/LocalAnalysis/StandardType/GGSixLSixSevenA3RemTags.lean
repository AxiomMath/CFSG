module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3Round12Remaining

public section

namespace CFSG.StandardType

section Lie

@[expose] def GGSixLSixSevenConjA3Round12Rem : Prop :=
  GGSixLSixSevenConjA3At .E6 ∧ GGSixLSixSevenConjA3At .F4 ∧ GGSixLSixSevenConjA3At .twistedE6

end Lie

section Assembly

theorem ggSixLSixSevenConjA3Round12_of_rem (h : GGSixLSixSevenConjA3Round12Rem) :
    GGSixLSixSevenConjA3Round12 :=
  ggSixLSixSevenConjA3Round12_of_remaining_three h.1 h.2.1 h.2.2

end Assembly

end CFSG.StandardType
