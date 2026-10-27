module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmFieldMinus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalURest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Rest

@[expose] def GGSixLSixElevenKGRest8 : Prop :=
  GGOrdPInnerConjPSpNonsplit ∧ GGOrdPInnerConjPSUNonsplit ∧ GGOrdPInnerConjPOmegaPlusNonsplit ∧
    GGOrdPInnerConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPSpNonsplit ∧ GGOrdPFieldConjPSURest ∧ GGOrdPFieldConjPOmegaPlusRest ∧
    GGOrdPFieldConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .PSU ∧ GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧
    GGOrdPTrialityInput

theorem ggSixLSixElevenKGRest7_of_rest8 (h : GGSixLSixElevenKGRest8) :
    GGSixLSixElevenKGRest7 := by
  obtain ⟨hSp, hU, hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, hO1, hO2, hO3, hT⟩ := h
  refine ⟨hSp, hU, fun t ht htL htp htu => ?_, hFSp, hFU, fun t ht htL htp htu => ?_, hO1, hO2,
    hO3, hT⟩
  · by_cases hP : t = .POmegaPlus
    · subst hP
      exact ggOrdPInnerConjAt_POmegaPlus_of_nonsplit hOP
    · by_cases hM : t = .POmegaMinus
      · subst hM
        exact ggOrdPInnerConjAt_POmegaMinus_of_nonsplit hOM
      · exact hI t ht htL htp htu hP hM
  · by_cases hP : t = .POmegaPlus
    · subst hP
      exact ggOrdPFieldConjAt_POmegaPlus_of_rest hFOP
    · by_cases hM : t = .POmegaMinus
      · subst hM
        exact ggOrdPFieldConjAt_POmegaMinus_of_nonsplit hFOM
      · exact hF t ht htL htp htu hP hM

end Rest

section Exc

theorem ggSixLSixElevenKGInput_of_rest8 (h : GGSixLSixElevenKGRest8) :
    GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest7 (ggSixLSixElevenKGRest7_of_rest8 h)

end Exc

end CFSG.StandardType
