module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLbar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOne
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLie
import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K1 K2 K5A9 K5J3 K5U42 K6a K6b LieFam811 IsLieFam811 IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

private theorem isLieFam811_psp6 {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .PSp 3 r f) : IsLieFam811 X .psp6 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, hr3, h⟩

private theorem isLieFam811_omega7 {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .POmegaOdd 3 r f) : IsLieFam811 X .omega7 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1,
    (CFSG.Blueprint.LieModel.admissible h).2.2.2, hr3, h⟩

private theorem isLieFam811_pomega8m {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .POmegaMinus 4 r f) : IsLieFam811 X .pomega8m r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, hr3, h⟩

private theorem isLieFam811_l4_psl {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 1)
    (h : LieModel X .PSL 4 r f) : IsLieFam811 X .l4 r f := by
  refine ⟨(CFSG.Blueprint.LieModel.admissible h).1, ?_, Or.inl ⟨hmod, h⟩⟩
  rintro h2
  rw [h2] at hmod
  norm_num at hmod

private theorem isLieFam811_l4_psu {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 2)
    (hne2 : r ^ f ≠ 2) (h : LieModel X .PSU 4 r f) : IsLieFam811 X .l4 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, hne2, Or.inr ⟨hmod, h⟩⟩

private theorem isLieFam811_l6_psl {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 2)
    (h : LieModel X .PSL 6 r f) : IsLieFam811 X .l6 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, Or.inl ⟨hmod, h⟩⟩

private theorem isLieFam811_l6_psu {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 1)
    (h : LieModel X .PSU 6 r f) : IsLieFam811 X .l6 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, Or.inr ⟨hmod, h⟩⟩

private theorem isLieFam811_l7_psl {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 2)
    (h : LieModel X .PSL 7 r f) : IsLieFam811 X .l7 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, Or.inl ⟨hmod, h⟩⟩

private theorem isLieFam811_l7_psu {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 1)
    (h : LieModel X .PSU 7 r f) : IsLieFam811 X .l7 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, Or.inr ⟨hmod, h⟩⟩

namespace Ctx82E3

theorem case811Exit_of_quasisimpleModOTwo (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK1 : K1) (hK2 : K2)
    (hA9 : K5A9) (hJ3 : K5J3) (hU42 : K5U42) :
    ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar ∨
    (¬ 3 ∣ Nat.card (Subgroup.center c.Lbar) ∧
      (LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3 ∨
        IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 10 ∨
        IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 11 ∨
        ∃ (fam : LieFam811) (r f : ℕ), IsLie811 c.Lbar fam r f)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨p, hp⟩ := c.sig_nonempty
  have h76 := c.conclusion76 hp
  have hqs : CFSG.Open.IsQuasisimple c.Lbar := c.isQuasisimple_lbar h811
  have hqsC : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff c.Lbar).2.2.1.mpr hqs
  have hcat : CFSG.Open.IsCatalogGroup (c.Lbar ⧸ Subgroup.center c.Lbar) :=
    c.isCatalogGroup_lbar h811
  have hodd : Odd (Nat.card (Subgroup.center c.Lbar)) := c.odd_card_center_lbar
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup c.Lbar) = 3 := c.pRank_three_lbar
  by_cases hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar
  · exact Or.inl hON
  · rcases hK1 c.Lbar hqs hcat hodd hrank with hON' | ⟨hZ, hrest⟩
    · exact absurd hON' hON
    · refine Or.inr ⟨hZ, ?_⟩
      by_cases h227 : LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3
      · exact Or.inl h227
      · rcases hrest with hsmall | hthree | hfour | hj3
        ·
          rcases hsmall with h9 | h10 | h11
          · exact (c.false_of_small h811 hK2 hA9 hJ3 hU42 hZ hON h227 hp h76
              (Or.inl h9)).elim
          · exact Or.inr (Or.inl h10)
          · exact Or.inr (Or.inr (Or.inl h11))
        ·
          rcases hthree with h227' | hpsp
          · exact absurd h227' h227
          · exact (c.false_of_small h811 hK2 hA9 hJ3 hU42 hZ hON h227 hp h76
              (Or.inr (Or.inr hpsp))).elim
        ·
          refine Or.inr (Or.inr (Or.inr ?_))
          rcases hfour with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
          · obtain ⟨r, f, hr3, hm⟩ := h1
            exact ⟨.psp6, r, f, hqsC, hodd, isLieFam811_psp6 hr3 hm⟩
          · obtain ⟨r, f, hr3, hm⟩ := h2
            exact ⟨.pomega8m, r, f, hqsC, hodd, isLieFam811_pomega8m hr3 hm⟩
          · obtain ⟨r, f, hmod, hm⟩ := h3
            exact ⟨.l4, r, f, hqsC, hodd, isLieFam811_l4_psl hmod hm⟩
          · obtain ⟨r, f, hmod, hne2, hm⟩ := h4
            exact ⟨.l4, r, f, hqsC, hodd, isLieFam811_l4_psu hmod hne2 hm⟩
          · obtain ⟨r, f, hmod, hm⟩ := h5
            exact ⟨.l6, r, f, hqsC, hodd, isLieFam811_l6_psl hmod hm⟩
          · obtain ⟨r, f, hmod, hm⟩ := h6
            exact ⟨.l6, r, f, hqsC, hodd, isLieFam811_l6_psu hmod hm⟩
          · obtain ⟨r, f, hmod, hm⟩ := h7
            exact ⟨.l7, r, f, hqsC, hodd, isLieFam811_l7_psl hmod hm⟩
          · obtain ⟨r, f, hmod, hm⟩ := h8
            exact ⟨.l7, r, f, hqsC, hodd, isLieFam811_l7_psu hmod hm⟩
          · obtain ⟨r, f, hr3, hm⟩ := h9
            exact ⟨.omega7, r, f, hqsC, hodd, isLieFam811_omega7 hr3 hm⟩
        ·
          exact (c.false_of_small h811 hK2 hA9 hJ3 hU42 hZ hON h227 hp h76
            (Or.inr (Or.inl hj3))).elim

theorem nonempty_case811Sylow_of_lie (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK2 : K2) (hK6a : K6a)
    (hK6b : K6b) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar))
    (hON : ¬ ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (h227 : ¬ LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f) :
    Nonempty (Case811Sylow c) := by
  have hPL : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M → P ≤ c.L :=
    fun P hP => c.le_L_of_K2 h811 hK2 hZ hON h227 hP
  exact c.exists_case811Sylow_of_K6 hK6a hK6b hlie hPL

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
