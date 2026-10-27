module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagSU
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalURest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Rest

@[expose] def GGSixLSixElevenKGRestOutdiag : Prop :=
  GGOrdPInnerConjPSpNonsplit ∧ GGOrdPInnerConjPSUNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPSpNonsplit ∧ GGOrdPFieldConjPSURest ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧ GGOrdPTrialityInput

theorem ggSixLSixElevenKGRest7_of_restOutdiag (h : GGSixLSixElevenKGRestOutdiag) :
    GGSixLSixElevenKGRest7 := by
  obtain ⟨hSp, hU, hI, hFSp, hFU, hF, hO2, hO3, hT⟩ := h
  exact ⟨hSp, hU, hI, hFSp, hFU, hF, ggOrdPOutdiagAt_PSU, hO2, hO3, hT⟩

theorem ggSixLSixElevenKGRest7_of_parts (hSp : GGOrdPInnerConjPSpNonsplit)
    (hU : GGOrdPInnerConjPSUNonsplit)
    (hI : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → GGOrdPInnerConjAt t)
    (hFSp : GGOrdPFieldConjPSpNonsplit) (hFU : GGOrdPFieldConjPSURest)
    (hF : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → GGOrdPFieldConjAt t)
    (hO2 : GGOrdPOutdiagAt .E6) (hO3 : GGOrdPOutdiagAt .twistedE6) (hT : GGOrdPTrialityInput) :
    GGSixLSixElevenKGRest7 :=
  ggSixLSixElevenKGRest7_of_restOutdiag ⟨hSp, hU, hI, hFSp, hFU, hF, hO2, hO3, hT⟩

end Rest

section Exc

theorem ggSixLSixElevenKGInput_of_restOutdiag (h : GGSixLSixElevenKGRestOutdiag) :
    GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest7 (ggSixLSixElevenKGRest7_of_restOutdiag h)

end Exc

end CFSG.StandardType
