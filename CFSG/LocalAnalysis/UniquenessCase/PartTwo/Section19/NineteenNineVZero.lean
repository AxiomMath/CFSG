module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineEngine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_V0_of_not_thin {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h127 : R127 D) (h869 : F08.R869 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnt : ¬ F08.Thin8 L) : L ≤ centralizer (V₀ : Set G) := by
  have hV11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 hV
  obtain ⟨-, -, hV₀n, -⟩ := uc22p22q_hyp11_unpack D hV11
  have hLX : L ≤ conjClosure D.M L := TwelveTwentyThree.le_conjClosure D.M L
  have hntX : ¬ F08.Thin8 (conjClosure D.M L) := fun hthin =>
    hnt fun q hq hq2 => (CFSG.SectionRank.pRank_mono hq.one_lt hLX).trans (hthin q hq hq2)
  exact hLX.trans (ElevenNine.le_centralizer_of_not_thin D h869 hV₀n
    (ElevenNine.card_le_four_or_eight_le D hV11) (ElevenNine.not_uniqueMax_of_eight_le D hV11)
    hL rfl hntX)

theorem le_centralizer_V0_of_shape19_9 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h127 : R127 D) (h869 : F08.R869 D)
    {n : ℕ} (hn : (IsU5 (Bar2 L) n ∧ n = 2) ∨ IsU4 (Bar2 L) n) :
    L ≤ centralizer (V₀ : Set G) := by
  refine le_centralizer_V0_of_not_thin h.hyp125 h127 h869 (S17.calLp_subset_calC D p h.hL) ?_
  rcases hn with ⟨hU5, -⟩ | hU4
  · exact S17.not_thin8_of_isU5_bar2 hU5
  · exact S17.not_thin8_of_isU4_bar2 hU4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
