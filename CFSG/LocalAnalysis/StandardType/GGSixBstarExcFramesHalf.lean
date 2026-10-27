module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
  ExcFramesHalf

theorem ggExcHalfLabel_large_or_small {τ : StatedLieTag} {t : StatedLieTag} {f p : ℕ}
    (h : t = τ ∧ p ∣ 2 ^ f + 1) :
    (t = τ ∧ p ∣ 2 ^ f + 1 ∧ p ≠ 3 ∧ p ≠ 5) ∨ (t = τ ∧ p ∣ 2 ^ f + 1 ∧ (p = 3 ∨ p = 5)) := by
  by_cases hs : p = 3 ∨ p = 5
  · exact Or.inr ⟨h.1, h.2, hs⟩
  · have hs' := not_or.mp hs
    exact Or.inl ⟨h.1, h.2, hs'.1, hs'.2⟩

section Frames

theorem ggSixBstarExcFrameOn_E8Half_of_rank
    (h : GGExcHalfBstarRankOn .E8 GGExcE8HalfSmallLabel) :
    GGSixBstarExcFrameOn .E8 GGExcE8HalfLabel :=
  ggSixBstarExcFrameOn_E8Half_of_rankOn (fun _ _ _ _ h => h)
    (GGExcHalfBstarRankOn.of_or ggExcHalfBstarRankOn_E8Large h fun _ _ _ _ hP =>
      ggExcHalfLabel_large_or_small hP)

theorem ggSixBstarExcFrameOn_E7Half_of_rank
    (h : GGExcHalfBstarRankOn .E7 GGExcE7HalfSmallLabel) :
    GGSixBstarExcFrameOn .E7 GGExcE7HalfLabel :=
  ggSixBstarExcFrameOn_E7Half_of_rankOn (fun _ _ _ _ h => h)
    (GGExcHalfBstarRankOn.of_or ggExcHalfBstarRankOn_E7Large h fun _ _ _ _ hP =>
      ggExcHalfLabel_large_or_small hP)

@[expose] def GGSixBstarExcFramesRestHalf : Prop :=
  GGExcNonsplitRankInput .F4 ∧
    GGExcHalfBstarRankOn .E7 GGExcE7HalfSmallLabel ∧ GGExcNonsplitRankInput .E7 ∧
      GGExcHalfBstarRankOn .E8 GGExcE8HalfSmallLabel ∧
        GGSixBstarExcFrameOn .E8 GGExcE8RestLabel ∧
          GGSixBstarExcFrameOn .E6 GGExcE6SplitLabel ∧
            GGSixBstarExcFrameOn .F4 GGExcE6NonsplitLabel ∧
              GGSixBstarExcFrameOn .E6 GGExcTwE6SplitLabel ∧
                GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitLabel

theorem ggSixBstarExcFramesRest_of_half (h : GGSixBstarExcFramesRestHalf) :
    GGSixBstarExcFramesRest := by
  obtain ⟨hF4N, hE7R, hE7N, hE8R, hE8N, hE6S, hE6N, hTwS, hTwN⟩ := h
  exact ⟨ggSixBstarExcFrameOn_F4Half, hF4N, ggSixBstarExcFrameOn_E7Half_of_rank hE7R, hE7N,
    ggSixBstarExcFrameOn_E8Half_of_rank hE8R, hE8N, hE6S, hE6N, hTwS, hTwN⟩

end Frames

end CFSG.StandardType
