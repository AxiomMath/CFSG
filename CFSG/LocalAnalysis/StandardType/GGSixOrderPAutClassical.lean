module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalGraphPlus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalGraphMinus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalInnerSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalFieldSp
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Rest

@[expose] def GGSixLSixElevenKGRest6 : Prop :=
  GGOrdPInnerConjPSpNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPSpNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .PSU ∧ GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧
    GGOrdPTrialityInput

theorem ggOrdPInnerConjAt_of_rest6 (h : GGSixLSixElevenKGRest6) (t : StatedLieTag)
    (ht : ¬ GGOrdPSmallTag t) (htL : t ≠ .PSL) : GGOrdPInnerConjAt t := by
  by_cases htp : t = .PSp
  · subst htp
    exact ggOrdPInnerConjAt_PSp_of_nonsplit h.1
  · exact h.2.1 t ht htL htp

theorem ggOrdPFieldConjAt_of_rest6 (h : GGSixLSixElevenKGRest6) (t : StatedLieTag)
    (ht : ¬ GGOrdPSmallTag t) (htL : t ≠ .PSL) : GGOrdPFieldConjAt t := by
  by_cases htp : t = .PSp
  · subst htp
    exact ggOrdPFieldConjAt_PSp_of_nonsplit h.2.2.1
  · exact h.2.2.2.1 t ht htL htp

theorem ggSixLSixElevenKGRound5_of_rest6 (h : GGSixLSixElevenKGRest6) :
    GGSixLSixElevenKGRound5 := by
  obtain ⟨-, -, -, -, hU, hE6, hTw, h5⟩ := id h
  exact ⟨ggOrdPInnerConjAt_of_rest6 h, ggOrdPFieldConjAt_of_rest6 h, hU, hE6, hTw,
    ggOrdPGraphAt_POmegaPlus, ggOrdPGraphAt_POmegaMinus, h5⟩

end Rest

section Exc

theorem ggOrdPGraphAt_all (t : StatedLieTag) : GGOrdPGraphAt t :=
  ggOrdPGraphAt_of_orthogonal ggOrdPGraphAt_POmegaPlus ggOrdPGraphAt_POmegaMinus t

theorem ggSixLSixElevenKGInput_of_rest6 (h : GGSixLSixElevenKGRest6) :
    GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_round5 (ggSixLSixElevenKGRound5_of_rest6 h)

end Exc

end CFSG.StandardType
