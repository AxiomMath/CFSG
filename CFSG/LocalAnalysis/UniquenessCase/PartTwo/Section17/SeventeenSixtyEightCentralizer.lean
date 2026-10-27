module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEight
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517B
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowAlt
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem pRank_eq_two_of_isA5xA5 {Q : Type} [Group Q] [Finite Q] (hQ : IsA5xA5 Q) {q : ℕ}
    (hq : q = 3 ∨ q = 5) : CFSG.Open.pRank q (⊤ : Subgroup Q) = 2 := by
  obtain ⟨e⟩ := hQ
  have hq1 : 1 < q := by rcases hq with rfl | rfl <;> norm_num
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq1 e]
  rcases hq with rfl | rfl
  · rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.Quasithin.H13.NQBlock.pRank_prod_eq Nat.prime_three,
      CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.RankThree.PartTwo.Sec4.RonanK432.alt_pRank_three_five]
  · rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.Quasithin.H13.NQBlock.pRank_prod_eq Nat.prime_five,
      CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_five_alternating_five]

theorem pRank_three_eq_one_of_isAlt_five {L : Subgroup G} (hAlt : IsAlt (Bar2 L) 5) :
    CFSG.Open.pRank 3 L = 1 := by
  obtain ⟨e⟩ := hAlt
  have hbar : CFSG.Open.pRank 3 (barImage L L) = CFSG.Open.pRank 3 L :=
    s13_pRank_barImage Nat.prime_three (by norm_num) le_rfl
  rw [← hbar, s13_barImage_self L,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.alt_pRank_three_five

theorem barImage_inf_centralizer_eq_bot {M X : Subgroup G}
    (hXA : IsA5xA5 ↥(barImage M X)) :
    barImage M X ⊓ Subgroup.centralizer (barImage M X : Set (Bar2 M)) = ⊥ :=
  CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center (center_eq_bot_of_isA5xA5 hXA)

theorem pRank_add_pRank_le_of_le_centralizer {D : Data G} {X : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hXA : IsA5xA5 ↥(barImage D.M X)) {C : Subgroup (Bar2 D.M)}
    (hC : C ≤ Subgroup.centralizer (barImage D.M X : Set (Bar2 D.M))) :
    CFSG.Open.pRank q (barImage D.M X) + CFSG.Open.pRank q C ≤
      CFSG.Open.pRank q (barImage D.M X ⊔ C) := by
  refine CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute hq ?_ ?_
  · intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hC hb) a ha
  · rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ barImage D.M X ⊓
        Subgroup.centralizer (barImage D.M X : Set (Bar2 D.M)) := ⟨hx.1, hC hx.2⟩
    rw [barImage_inf_centralizer_eq_bot hXA] at hx'
    exact hx'

theorem pRank_centralizer_le_one {D : Data G} {X : Subgroup G} {q : ℕ}
    (hq : q = 3 ∨ q = 5) (he3 : CFSG.Open.evenRank G = 3)
    (hXA : IsA5xA5 ↥(barImage D.M X)) :
    CFSG.Open.pRank q (Subgroup.centralizer (barImage D.M X : Set (Bar2 D.M))) ≤ 1 := by
  have hprime : q.Prime := by rcases hq with rfl | rfl <;> norm_num
  have hq2 : q ≠ 2 := by rcases hq with rfl | rfl <;> norm_num
  have hadd := pRank_add_pRank_le_of_le_centralizer (D := D) (X := X) hprime hq2 hXA
    (C := Subgroup.centralizer (barImage D.M X : Set (Bar2 D.M))) le_rfl
  have hA : CFSG.Open.pRank q (barImage D.M X) = 2 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact pRank_eq_two_of_isA5xA5 hXA hq
  have htop : CFSG.Open.pRank q (barImage D.M X ⊔
      Subgroup.centralizer (barImage D.M X : Set (Bar2 D.M))) ≤ 3 := by
    calc CFSG.Open.pRank q (barImage D.M X ⊔
          Subgroup.centralizer (barImage D.M X : Set (Bar2 D.M)))
        ≤ CFSG.Open.pRank q (⊤ : Subgroup (Bar2 D.M)) :=
          CFSG.SectionRank.pRank_mono hprime.one_lt le_top
      _ = CFSG.Open.pRank q D.M := s13_pRank_bar_top hprime hq2 D.M
      _ ≤ eM D.M := pRank_le_eM_of_odd_prime hprime hq2
      _ ≤ CFSG.Open.evenRank G := eM_le_evenRank D
      _ = 3 := he3
  omega

theorem barImage_le_centralizer {D : Data G} {L L' J : Subgroup G}
    (hL : L ∈ calC D.M) (hL' : L' ∈ calC D.M) (hX : conjClosure D.M L = L ⊔ L')
    (hJ : J ∈ calC D.M) (hJL : J ≠ L) (hJL' : J ≠ L') :
    barImage D.M J ≤ Subgroup.centralizer
      (barImage D.M (conjClosure D.M L) : Set (Bar2 D.M)) := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hL'M : L' ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL'.1
  have hcommL : ∀ a ∈ barImage D.M L, ∀ b ∈ barImage D.M J, a * b = b * a :=
    fun a ha b hb => uc22p22l_barImage_commute hL hJ hJL.symm a ha b hb
  have hcommL' : ∀ a ∈ barImage D.M L', ∀ b ∈ barImage D.M J, a * b = b * a :=
    fun a ha b hb => uc22p22l_barImage_commute hL' hJ hJL'.symm a ha b hb
  rw [hX, s13_barImage_sup hLM hL'M, CFSG.centralizer_sup_eq]
  refine le_inf ?_ ?_
  · intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcommL a ha x hx
  · intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcommL' a ha x hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
