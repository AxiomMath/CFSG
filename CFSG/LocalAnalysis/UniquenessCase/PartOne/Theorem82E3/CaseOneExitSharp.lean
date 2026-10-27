module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL227Final
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.K5Sharp
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneONan
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K1 K2 K3Exp K3Out K4a K4b K5A9 K5J3 K5U42 LieFam811 IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3

private theorem sig_eq_singleton_of_forall_eq (c : Ctx82E3 D) {q : ℕ}
    (h : ∀ p ∈ D.sig, p = q) : D.sig = {q} := by
  obtain ⟨p, hp⟩ := c.sig_nonempty
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, h⟩
  rw [← h p hp]
  exact hp

theorem case811ExitSharp_of_quasisimpleModOTwo (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK1 : K1) (hK2 : K2)
    (hA9 : K5A9) (hJ3 : K5J3) (hU42 : K5U42) (hK3 : K3Exp) (hK3Out : K3Out) (hK4a : K4a)
    (hK4b : K4b) (hA10 : K5A10Sharp) (hA11 : K5A11Sharp) (hONS : K5ONanSharp) :
    (ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar ∧ D.sig = {7}) ∨
    (¬ 3 ∣ Nat.card (Subgroup.center c.Lbar) ∧
      (((IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 10 ∨ IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 11) ∧
          D.sig = {5}) ∨
        ∃ (fam : LieFam811) (r f : ℕ), IsLie811 c.Lbar fam r f)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hqsC : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff c.Lbar).2.2.1.mpr (c.isQuasisimple_lbar h811)
  have hodd : Odd (Nat.card (Subgroup.center c.Lbar)) := c.odd_card_center_lbar
  have hexit := c.case811Exit_of_quasisimpleModOTwo h811 hK1 hK2 hA9 hJ3 hU42
  by_cases hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar
  ·
    refine Or.inl ⟨hON, sig_eq_singleton_of_forall_eq c ?_⟩
    intro p hp
    by_contra hp7
    have hprime := (D.sig_prime p hp).1
    have h2 := c.two_le_pRank_range_of_threeCover_ONan hK3 (hK3Out c.Lbar hON) hON hp
      (c.conclusion76 hp)
    have hle : CFSG.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 1 :=
      hONS c.Lbar hON p hprime (c.five_le_of_mem_sigma hp) hp7
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank (p := p)
      (H := (⊤ : Subgroup (MulAut c.Lbar)))] at hle
    have hmono := CFSG.SectionRank.pRank_mono (p := p)
      (H := (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).range)
      (K := ⊤) hprime.one_lt le_top
    omega
  · obtain ⟨hZ, hrest⟩ := hexit.resolve_left hON
    refine Or.inr ⟨hZ, ?_⟩
    by_cases h227 : LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3
    · exact (c.false_of_L227 h811 hK4a hK4b h227 hZ).elim
    ·
      have hAlt : (IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 10 ∨
          IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 11) → D.sig = {5} := by
        intro hY
        refine sig_eq_singleton_of_forall_eq c ?_
        intro p hp
        by_contra hp5
        have hprime := (D.sig_prime p hp).1
        have h7 : 7 ≤ p := by
          have h5 := c.five_le_of_mem_sigma hp
          have h6 : p ≠ 6 := by
            rintro rfl
            norm_num at hprime
          omega
        obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
        have hPL : P ≤ c.L := c.le_L_of_K2 h811 hK2 hZ hON h227 hP
        have hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L := fun x hx _ => hPL hx
        have hle : CFSG.pRank p (⊤ : Subgroup (MulAut c.Lbar)) ≤ 1 := by
          rcases hY with h | h
          · exact hA10 c.Lbar hqsC hodd h p hprime h7
          · exact hA11 c.Lbar hqsC hodd h p hprime h7
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank (p := p)
          (H := (⊤ : Subgroup (MulAut c.Lbar)))] at hle
        exact c.false_of_pRank_mulAut_lbar_le_one hp (c.conclusion76 hp) hP hΩ hle
      rcases hrest.resolve_left h227 with h10 | h11 | hlie
      · exact Or.inl ⟨Or.inl h10, hAlt (Or.inl h10)⟩
      · exact Or.inl ⟨Or.inr h11, hAlt (Or.inr h11)⟩
      · exact Or.inr hlie

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
