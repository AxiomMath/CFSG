module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpack
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.GroupTheory.WeirSylow.CrossRankUnitary
import CFSG.RankThree.PartOne.KF.F128OmegaRank
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (LieFam811 IsLie811 center_eq_bot_of_isLie811)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelUnpack
open CFSG.GroupTheory.WeirSylow

private theorem two_pow_sq (f : ℕ) : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by
  rw [← pow_mul, Nat.mul_comm]

private theorem pRank_psp6_le_one {K : Type} [Field K] [Finite K] [CharP K 2] {f p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ f) (hpq : ¬ p ∣ 2 ^ f)
    (hpq2 : ¬ p ∣ 2 ^ (2 * f) - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp 3 K))) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card K := by rw [hK]; exact hpq
  have hpK2 : ¬ p ∣ Nat.card K ^ 2 - 1 := by rw [hK, two_pow_sq]; exact hpq2
  have he3 : 3 ≤ orderOf (Nat.card K : ZMod p) := by
    rw [← ordMod_natCast]
    exact three_le_ordMod_of_not_dvd_sq_sub_one (by exact_mod_cast hpK)
      (not_intCast_dvd_sq_sub_one_of_not_dvd hpK2)
  rw [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_Sp_formula
    (n := 3) hp (by omega) hpK]
  split_ifs with hev
  · rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < orderOf (Nat.card K : ZMod p))]
    rcases hev with ⟨k, hk⟩
    omega
  · exact Nat.div_le_of_le_mul (by omega)

private theorem pRank_pomega8m_le_one {K : Type} [Field K] [Finite K] [CharP K 2] {f p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ f) (hpq2 : ¬ p ∣ 2 ^ (2 * f) - 1)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Open.pRank p
      (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus 4 K b c)))) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq2' : ¬ p ∣ (2 ^ f) ^ 2 - 1 := by rw [two_pow_sq]; exact hpq2
  have hq1 : ¬ p ∣ 2 ^ f - 1 := fun h =>
    hq2' (h.trans (by simpa using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2))
  have hq1' : ¬ p ∣ 2 ^ f + 1 := fun h =>
    hq2' (h.trans (by
      rw [show (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) by
        simpa using Nat.sq_sub_sq (2 ^ f) 1]
      exact dvd_mul_right _ _))
  have h1 : ¬ p ∣ Nat.card K - 1 := by rwa [hK]
  have h2 : ¬ p ∣ Nat.card K + 1 := by rwa [hK]
  have hb := CFSG.RankThree.PartOne.pRank_statedProj_statedOmegaMinus_four_le_one
    hbc hp hp5 h1 h2
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at hb

private theorem pRank_psl4_le_one {K : Type} [Field K] [Finite K] [CharP K 2] {f p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ f) (hpq : ¬ p ∣ 2 ^ f)
    (hpq2 : ¬ p ∣ 2 ^ (2 * f) - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL 4 K))) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Nat.card K := by rw [hK]; exact hpq
  have hpK2 : ¬ p ∣ Nat.card K ^ 2 - 1 := by rw [hK, two_pow_sq]; exact hpq2
  have hb := pRank_top_statedProj_le_card_div_three (p := p) (hp.odd_of_ne_two (by omega)) hpK
    hpK2 (StatedSL 4 K)
  simpa using hb

private theorem pRank_psu4_le_one {K : Type} [Field K] [Finite K] [CharP K 2] {f p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = (2 ^ f) ^ 2) (hpq : ¬ p ∣ 2 ^ f)
    (hpq2 : ¬ p ∣ 2 ^ (2 * f) - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K))) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq2' : ¬ p ∣ (2 ^ f) ^ 2 - 1 := by rw [two_pow_sq]; exact hpq2
  have hb := pRank_top_statedProj_statedSU_le_div_three (p := p) (L := K) (q := 2 ^ f)
    (n := 4) (hp.odd_of_ne_two (by omega)) hK hpq hpq2' (by norm_num)
  simpa using hb

theorem k7cSharp_holds :
    K7cSharp := by
  intro Y _ _ fam f hfam hY p hp hp5 hndvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : fam ≠ .l7 := by rcases hfam with h | h | h <;> rw [h] <;> decide
  have hZ : center Y = ⊥ := center_eq_bot_of_isLie811 hY hne
  have hZdiv : ¬ p ∣ Nat.card (center Y) := by
    rw [hZ, Subgroup.card_bot]
    exact hp.not_dvd_one
  have hquot : CFSG.pRank p (⊤ : Subgroup Y) =
      CFSG.pRank p (⊤ : Subgroup (Y ⧸ center Y)) := by
    simp only [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_quotient_eq (center Y) hZdiv).symm
  have hpq : ¬ p ∣ 2 ^ f := fun h => hndvd (h.mul_right _)
  have hpq2 : ¬ p ∣ 2 ^ (2 * f) - 1 := fun h => hndvd (h.mul_left _)
  rw [hquot, CFSG.SectionRank.pRank_coe_eq_openPRank]
  rcases hfam with rfl | rfl | rfl
  · obtain ⟨-, -, hm⟩ := hY.2.2
    obtain ⟨K, _, _, _, hK, -, ⟨e⟩⟩ :=
      exists_model_of_lieModel_psp (by norm_num : (2 : ℕ) ≠ 3) hm
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact pRank_psp6_le_one hp hp5 hK hpq hpq2
  · obtain ⟨-, -, hm⟩ := hY.2.2
    obtain ⟨K, _, _, _, hK, -, b, c, hbc, ⟨e⟩⟩ :=
      exists_model_of_lieModel_pomegaMinus (by norm_num : (2 : ℕ) ≠ 3) hm
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact pRank_pomega8m_le_one hp hp5 hK hpq2 hbc
  · obtain ⟨-, -, hcase⟩ := hY.2.2
    rcases hcase with ⟨-, hm⟩ | ⟨-, hm⟩
    · obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
        exists_model_of_lieModel_psl (by norm_num : (4 : ℕ) ≠ 0) hm
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
      exact pRank_psl4_le_one hp hp5 hK hpq hpq2
    · obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
        exists_model_of_lieModel_psu (by norm_num : (4 : ℕ) ≠ 0) hm
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
      exact pRank_psu4_le_one hp hp5 hK hpq hpq2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
