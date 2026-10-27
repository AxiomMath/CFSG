module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmRest
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSU
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Rest

@[expose] def GGSixLSixElevenKGRest9 : Prop :=
  GGOrdPInnerConjPOmegaPlusNonsplit ∧ GGOrdPInnerConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPSpNonsplit ∧ GGOrdPFieldConjPSURest ∧ GGOrdPFieldConjPOmegaPlusRest ∧
    GGOrdPFieldConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .PSU ∧ GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧
    GGOrdPTrialityInput

theorem ggSixLSixElevenKGRest8_of_rest9 (h : GGSixLSixElevenKGRest9) :
    GGSixLSixElevenKGRest8 := by
  obtain ⟨hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, hO1, hO2, hO3, hT⟩ := h
  exact ⟨ggOrdPInnerConjPSpNonsplit_holds, ggOrdPInnerConjPSUNonsplit_holds, hOP, hOM, hI, hFSp,
    hFU, hFOP, hFOM, hF, hO1, hO2, hO3, hT⟩

end Rest

section Exc

theorem ggSixLSixElevenKGInput_of_rest9 (h : GGSixLSixElevenKGRest9) :
    GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest8 (ggSixLSixElevenKGRest8_of_rest9 h)

end Exc

end CFSG.StandardType
