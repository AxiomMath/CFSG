module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneOuter
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KeyLemma
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

variable {G : Type} [Group G] [Finite G]

namespace Counterexample4

variable (c : Counterexample4 G)

abbrev Lbar : Type := ↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L

theorem isKGroup_lbar : CFSG.Open.IsKGroup c.Lbar := by
  have hL_ne_top : c.L ≠ ⊤ := by
    intro htop
    exact c.M_ne_top (top_le_iff.mp (htop ▸ c.hyp81.1))
  have hK : CFSG.Open.IsKGroup ↥c.L := c.standing.kProper.isKGroup c.L hL_ne_top
  exact hK.quotient (CFSG.Open.pCore 2 ↥c.L)

theorem odd_card_center_lbar : Odd (Nat.card (Subgroup.center c.Lbar)) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center c.Lbar) 2 h2
  have hzord : orderOf (z : c.Lbar) = 2 := by
    rw [Subgroup.orderOf_coe, hz]
  have hcard : Nat.card (Subgroup.zpowers (z : c.Lbar)) = 2 := by
    rw [Nat.card_zpowers, hzord]
  have hp2 : IsPGroup 2 (Subgroup.zpowers (z : c.Lbar)) :=
    IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have hnormal : (Subgroup.zpowers (z : c.Lbar)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2)
  have hle : Subgroup.zpowers (z : c.Lbar) ≤ CFSG.Open.pCore 2 c.Lbar := by
    change Subgroup.zpowers (z : c.Lbar) ≤
      sSup {K : Subgroup c.Lbar | K.Normal ∧ IsPGroup 2 K}
    exact le_sSup (s := {K : Subgroup c.Lbar | K.Normal ∧ IsPGroup 2 K}) ⟨hnormal, hp2⟩
  have hcore : CFSG.Open.pCore 2 c.Lbar = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (p := 2) (H := ↥c.L)
  have hz_one : (z : c.Lbar) = 1 := by
    have hmem : (z : c.Lbar) ∈ (⊥ : Subgroup c.Lbar) := by
      rw [← hcore]
      exact hle (Subgroup.mem_zpowers (z : c.Lbar))
    simpa using hmem
  have : orderOf (z : c.Lbar) = 1 := by rw [hz_one]; exact orderOf_one
  omega

theorem pRank_three_lbar : CFSG.Open.pRank 3 (⊤ : Subgroup c.Lbar) = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥c.L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L))
      Nat.prime_three (by norm_num)
  rw [CFSG.SectionRank.pRank_quotient_eq (p := 3) (N := CFSG.Open.pCore 2 ↥c.L) h3,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup c.L]
  exact c.pRank_three_L

theorem isQuasisimple_lbar (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) :
    CFSG.Open.IsQuasisimple c.Lbar := by
  simpa [Lbar] using h811.2

theorem isCatalogGroup_lbar (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) :
    CFSG.Open.IsCatalogGroup (c.Lbar ⧸ Subgroup.center c.Lbar) := by
  have hq := isQuasisimple_lbar c h811
  haveI : IsSimpleGroup (c.Lbar ⧸ Subgroup.center c.Lbar) := hq.2
  have hnab : ∃ a b : c.Lbar ⧸ Subgroup.center c.Lbar, a * b ≠ b * a := by
    have hp : Group.IsPerfect c.Lbar := (Group.isPerfect_def).2 hq.1
    have hc : ¬ IsMulCommutative (c.Lbar ⧸ Subgroup.center c.Lbar) :=
      Group.IsPerfect.not_isMulCommutative (c.Lbar ⧸ Subgroup.center c.Lbar)
    simpa only [isMulCommutative_iff, not_forall] using hc
  exact CFSG.Open.IsKGroup.isCatalogGroup_of_surjective (isKGroup_lbar c) ⊤ hnab
    ((QuotientGroup.mk' (Subgroup.center c.Lbar)).comp
      (Subgroup.topEquiv (G := c.Lbar)).toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := c.Lbar)).surjective)

theorem le_L_of_K2 (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK2 : K2)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar))
    (hON : ¬ ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (h227 : ¬ LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) : P ≤ c.L := by
  have hq : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff c.Lbar).2.2.1.mpr (isQuasisimple_lbar c h811)
  have hp3 : CFSG.pRank 3 (⊤ : Subgroup c.Lbar) = 3 :=
    (CFSG.SectionRank.pRank_coe_eq_openPRank (p := 3) (H := (⊤ : Subgroup c.Lbar))).trans
      (pRank_three_lbar c)
  refine le_L_of_isSylowOf c hZ ?_ hP
  intro R hR hRinf hRnot
  have h4 := hK2 c.Lbar hq (isCatalogGroup_lbar c h811)
    (odd_card_center_lbar c) hp3 hON h227 R hR hRinf hRnot
  rwa [CFSG.SectionRank.pRank_coe_eq_openPRank (p := 3) (H := R)] at h4

theorem false_of_pRank_mulAut_lbar_le_two {p : ℕ} (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M)
    (hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L)
    (h2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 2) : False := by
  have h3 := three_le_pRank_range_of_forall_pow_eq_one c hp h76 hP hΩ
  have hle := CFSG.SectionRank.pRank_mono (p := p)
    (H := (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).range)
    (K := ⊤) hp.1.1.one_lt le_top
  omega

theorem false_of_small (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK2 : K2)
    (hK5 : K5) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar))
    (hON : ¬ ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (h227 : ¬ LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    {p : ℕ} (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (hY : IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 9 ∨
      IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 10 ∨
      IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 11 ∨
      IsSpor (c.Lbar ⧸ Subgroup.center c.Lbar) .J3 ∨
      LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSp 2 3 1) : False := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 c.S.M
  have hPL : P ≤ c.L := le_L_of_K2 c h811 hK2 hZ hON h227 hP
  have hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L := fun x hx _ => hPL hx
  have hqs : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff c.Lbar).2.2.1.mpr (isQuasisimple_lbar c h811)
  have hodd := odd_card_center_lbar c
  have hp5 := c.five_le_of_mem_sigma hp
  have hprime := hp.1.1
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 2 := by
    rcases hY with h | h | h | h | h
    · have hle : CFSG.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 1 :=
        hK5.1 c.Lbar hqs hodd h p hprime hp5
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank (p := p)
        (H := (⊤ : Subgroup (MulAut c.Lbar)))] at hle
      omega
    · have hle : CFSG.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 2 :=
        hK5.2.1 c.Lbar hqs hodd h p hprime hp5
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank (p := p)
        (H := (⊤ : Subgroup (MulAut c.Lbar)))] at hle
      omega
    · have hle : CFSG.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 2 :=
        hK5.2.2.1 c.Lbar hqs hodd h p hprime hp5
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank (p := p)
        (H := (⊤ : Subgroup (MulAut c.Lbar)))] at hle
      omega
    · have hle : CFSG.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 1 :=
        hK5.2.2.2.1 c.Lbar hqs hodd h p hprime hp5
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank (p := p)
        (H := (⊤ : Subgroup (MulAut c.Lbar)))] at hle
      omega
    · have hle : CFSG.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 1 :=
        hK5.2.2.2.2.2.1 c.Lbar hqs hodd h p hprime hp5
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank (p := p)
        (H := (⊤ : Subgroup (MulAut c.Lbar)))] at hle
      omega
  exact false_of_pRank_mulAut_lbar_le_two c hp h76 hP hΩ h2

end Counterexample4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
