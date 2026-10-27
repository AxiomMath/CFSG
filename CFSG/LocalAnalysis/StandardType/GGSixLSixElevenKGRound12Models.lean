module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenKGModelInputs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenKGRound12Reduction
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRank
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankE7
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankE8

public section

namespace CFSG.StandardType

open CFSG.Open (StatedLieTag)

section Full

theorem ggOrdPFieldConj_of_two
    (h : ∀ t : StatedLieTag, (t = .E6 ∨ t = .twistedE6) → GGOrdPFieldConjAt t) :
    ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t := by
  intro t hs h1 h2 h3 h4 h5
  by_cases hF4 : t = .F4
  · subst hF4
    exact ggOrdPFieldConjAt_of_centRank ggExcFieldAutCentRank_F4
  by_cases hE7 : t = .E7
  · subst hE7
    exact ggOrdPFieldConjAt_of_centRank ggExcFieldAutCentRank_E7
  by_cases hE8 : t = .E8
  · subst hE8
    exact ggOrdPFieldConjAt_of_centRank ggExcFieldAutCentRank_E8
  exact h t (by cases t <;> simp_all [GGOrdPSmallTag])

theorem ggSixLSixElevenKGRound12_of_models
    (hF4 : GGOrdPToralF4RestHard) (hE6 : GGOrdPToralE6RestHard) (hE7 : GGOrdPToralE7RestHard)
    (hE8 : GGOrdPToralE8RestHard) (hTw : GGOrdPToralTwE6RestHard)
    (hF : ∀ t : StatedLieTag, (t = .E6 ∨ t = .twistedE6) → GGOrdPFieldConjAt t)
    (hK1 : GGE6NontoralFixPpdInput) (hK2 : GGE6ToralFixNoPpdInput)
    (hF1 : GGTwE6FrameNoPpdInput) (hF2 : GGTwE6FrameFixPpdInput) :
    GGSixLSixElevenKGRound12 :=
  ggSixLSixElevenKGRound12_of_hard hF4 hE6 hE7 hE8 hTw (ggOrdPFieldConj_of_two hF)
    (ggOutdiagTwistedPpdAt_E6_of_input hK1) (ggOutdiagToralNoPpdAt_E6_of_input hK2)
    (ggOutdiagTwistedPpdAt_twistedE6_of_input hF2) (ggOutdiagToralNoPpdAt_twistedE6_of_input hF1)

theorem ggSixLSixElevenKGRound12_of_kg
    (h : GGSixLSixElevenKGModelInputs)
    (hF : ∀ t : StatedLieTag, (t = .E6 ∨ t = .twistedE6) → GGOrdPFieldConjAt t) :
    GGSixLSixElevenKGRound12 :=
  let ⟨hF4, hE6, hE7, hE8, hTw, hK1, hK2, hF1, hF2⟩ := h
  ggSixLSixElevenKGRound12_of_models hF4 hE6 hE7 hE8 hTw hF hK1 hK2 hF1 hF2

end Full

end CFSG.StandardType
