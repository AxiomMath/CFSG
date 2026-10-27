module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwelveDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralMax
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeHolds
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagExcPpd
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardF4
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardE6
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardE7
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardE8
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardTwE6

public section

namespace CFSG.StandardType

section Full

theorem ggSixLSixElevenKGRound12_of_hard
    (hF4 : GGOrdPToralF4RestHard) (hE6 : GGOrdPToralE6RestHard) (hE7 : GGOrdPToralE7RestHard)
    (hE8 : GGOrdPToralE8RestHard) (hTw : GGOrdPToralTwE6RestHard)
    (hF : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t)
    (hI6 : GGOutdiagTwistedPpdAt .E6 ggOutdiagExpsE6)
    (hII6 : GGOutdiagToralNoPpdAt .E6 ggOutdiagExpsE6)
    (hITw : GGOutdiagTwistedPpdAt .twistedE6 ggOutdiagExpsTwE6)
    (hIITw : GGOutdiagToralNoPpdAt .twistedE6 ggOutdiagExpsTwE6) :
    GGSixLSixElevenKGRound12 :=
  ⟨ggOrdPToralF4Rest_of_hard hF4, ggOrdPToralE6Rest_of_hard hE6, ggOrdPToralE7Rest_of_hard hE7,
    ggOrdPToralE8Rest_of_hard hE8, ggTwE6InndiagOrdPInnerInput_holds,
    ggTwE6CenterTrivialInput_holds, ggOrdPToralTwE6Input_of_rest (ggOrdPToralTwE6Rest_of_hard hTw),
    hF, ggOrdPOutdiagAt_E6_of_ppd hI6 hII6, ggOrdPOutdiagAt_twistedE6_of_ppd hITw hIITw,
    TriBridge.ggD4GraphFieldLayerInput_holds, TriBridge.ggD4GraphLayerInput_holds⟩

end Full

end CFSG.StandardType
