module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Quot
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8U42

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r925_two_lt_pRank_of_isU4 {X : Type} [Group X] [Finite X] (h : IsU4 X 1) :
    2 < CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨F, hF, hcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.UFourTwo.exists_isElemAbelian_card_27 h
  have h3 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : F ≤ ⊤) hF (k := 3)
    (by rw [hcard]; norm_num)
  omega

theorem r925_two_lt_pRank {L : Subgroup G} (hU : IsU4 (Bar2 L) 1) : 2 < CFSG.Open.pRank 3 L := by
  have h1 := r925_two_lt_pRank_of_isU4 hU
  have h2 := r925_pRank_quotient_le (CFSG.pCore 2 ↥L) Nat.prime_three
    (r925_pCore_two_orderOf Nat.prime_three (by norm_num))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  omega

theorem r925_hyp81 {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) (hU : IsU4 (Bar2 L) 1) :
    F08.Hyp81 D.M L :=
  ⟨hL.1, hL.2.1, r925_two_lt_pRank hU, Or.inl (A3.isQuasisimple_iff_open.mpr hL.2.2)⟩

theorem r925_strong_embed {D : Data G} (h82 : F08.R82 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hU : IsU4 (Bar2 L) 1) : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
  h82 L (r925_hyp81 hL hU)

theorem r925_normalizer_le {M : Subgroup G}
    (h : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M) {D : Subgroup G} (hD : D ≤ M)
    (hD3 : Nat.card D = 3) : normalizer (D : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDne : D ≠ ⊥ := fun h0 => by simp [h0] at hD3
  exact h.normalizer_le hDne (IsPGroup.of_card (n := 1) (by simpa using hD3)) hD

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
