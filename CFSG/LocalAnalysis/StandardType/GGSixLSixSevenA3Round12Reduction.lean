module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwelveDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3EntryPSLProof
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ExcRank

public section

namespace CFSG.StandardType

section Reduction


theorem ggSixLSixSevenConjA3Round12_of_remaining (hE6 : GGSixLSixSevenConjA3At .E6)
    (hU : GGSixLSixSevenConjA3At .PSU) (hSp : GGSixLSixSevenConjA3At .PSp)
    (hF4 : GGSixLSixSevenConjA3At .F4) (hTw : GGSixLSixSevenConjA3At .twistedE6) :
    GGSixLSixSevenConjA3Round12 :=
  ⟨ggSixLSixSevenConjA3At_PSL_of_entry ggSixLSixSevenA3EntryPSL_holds,
    ggSixLSixSevenConjA3At_POmegaPlus, hE6,
    ⟨hU, hSp, ggSixLSixSevenConjA3At_POmegaMinus, hF4, ggSixLSixSevenConjA3At_E7,
      ggSixLSixSevenConjA3At_E8, hTw⟩⟩

end Reduction

end CFSG.StandardType
