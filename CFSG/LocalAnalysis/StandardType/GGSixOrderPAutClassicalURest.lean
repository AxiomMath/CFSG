module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalUInner
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalUField
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Rest

@[expose] def GGSixLSixElevenKGRest7 : Prop :=
  GGOrdPInnerConjPSpNonsplit ∧ GGOrdPInnerConjPSUNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPSpNonsplit ∧ GGOrdPFieldConjPSURest ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .PSU ∧ GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧
    GGOrdPTrialityInput

theorem ggSixLSixElevenKGRest6_of_rest7 (h : GGSixLSixElevenKGRest7) :
    GGSixLSixElevenKGRest6 := by
  obtain ⟨hSp, hU, hI, hFSp, hFU, hF, hO1, hO2, hO3, hT⟩ := h
  refine ⟨hSp, fun t ht htL htp => ?_, hFSp, fun t ht htL htp => ?_, hO1, hO2, hO3, hT⟩
  · by_cases htu : t = .PSU
    · subst htu
      exact ggOrdPInnerConjAt_PSU_of_nonsplit hU
    · exact hI t ht htL htp htu
  · by_cases htu : t = .PSU
    · subst htu
      exact ggOrdPFieldConjAt_PSU_of_rest hFU
    · exact hF t ht htL htp htu

end Rest

section Exc

theorem ggSixLSixElevenKGInput_of_rest7 (h : GGSixLSixElevenKGRest7) :
    GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest6 (ggSixLSixElevenKGRest6_of_rest7 h)

end Exc

end CFSG.StandardType
