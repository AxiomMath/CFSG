module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeCentralCover
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
public import CFSG.Adapters.Certificate43Check

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianFamilies
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsThree
import CFSG.GroupTheory.PRankQuotientLift
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourLin
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourOrth

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

private theorem oddFree_K01 (hN : uc22p20rNativeGriess) (K : Type) [Group K] [Finite K]
    {t : StatedLieTag} {m f : ℕ} (hadm : StatedLieAdmissible t m 2 f)
    (hM : LieModel (K ⧸ Subgroup.center K) t m 2 f) (hq : CFSG.Open.IsQuasisimple K)
    (hodd : Odd (Nat.card (Subgroup.center K))) (h3 : 3 ∣ Nat.card (Subgroup.center K))
    (ht : t ∈ oddMultiplierFreeTags) : False := by
  have hgen := genericOrders_eq_one_of_mem_oddMultiplierFreeTags ht hadm
  have hc := uc22p20v_center_eq_bot hN hq hodd hM hgen
  rw [hc, Subgroup.card_bot] at h3
  exact absurd h3 (by norm_num)

private theorem psl_K01 (hN : uc22p20rNativeGriess) (K : Type) [Group K] [Finite K] {m f : ℕ}
    (hadm : StatedLieAdmissible .PSL m 2 f) (hM : LieModel (K ⧸ Subgroup.center K) .PSL m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K)))
    (h3 : 3 ∣ Nat.card (Subgroup.center K))
    (h3Q : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 3) :
    m = 3 ∧ Even f ∧ Nat.card (Subgroup.center K) = 3 ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨-, -, hm2, -, -⟩ := hadm
  have hdvd := uc22p20v_card_center_dvd hN hq hodd hM
  change Nat.card (Subgroup.center K) ∣ Nat.gcd m (2 ^ f - 1) * 1 at hdvd
  rw [mul_one] at hdvd
  have h3g : 3 ∣ Nat.gcd m (2 ^ f - 1) := h3.trans hdvd
  have hm3dvd : 3 ∣ m := h3g.trans (Nat.gcd_dvd_left _ _)
  have hsub : 3 ∣ 2 ^ f - 1 := h3g.trans (Nat.gcd_dvd_right _ _)
  have hfeven : Even f := by
    by_contra hf
    exact uc22p20v_not_three_dvd_sub_one (Nat.not_even_iff_odd.1 hf) hsub
  obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := LieModel.statedClassicalModel_of_ne_zero (by omega) hM
  have hm6 : ¬ 6 ≤ m := by
    intro hm6
    have h1 := four_le_pRank_projSL_of_dvd (F := K') (n := m) (by omega) (by
      rw [hK']; exact hsub)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e] at h1
    omega
  have hm_eq : m = 3 := by
    obtain ⟨k, hk⟩ := hm3dvd
    omega
  subst m
  have hZ : Nat.card (Subgroup.center K) = 3 :=
    Nat.dvd_antisymm (uc22p20v_center_dvd_three_psl hN hq hodd hM) h3
  have hmod : Nat.card K' % 3 = 1 := by
    rw [hK', uc22p20v_two_pow_mod_three_even hfeven]
  have h1 := psl_three_two_le_pRank_three (K := K') hmod
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e] at h1
  exact ⟨rfl, hfeven, hZ, CFSG.GroupTheory.two_le_pRank_of_quotient (Subgroup.center K)
    Nat.prime_three (by norm_num) h1⟩

private theorem psu_K01 (hN : uc22p20rNativeGriess) (K : Type) [Group K] [Finite K] {m f : ℕ}
    (hadm : StatedLieAdmissible .PSU m 2 f) (hM : LieModel (K ⧸ Subgroup.center K) .PSU m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K)))
    (h3 : 3 ∣ Nat.card (Subgroup.center K))
    (h3Q : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 3) : m = 3 ∧ Odd f := by
  obtain ⟨-, -, hm3, -⟩ := hadm
  have hdvd := uc22p20v_card_center_dvd hN hq hodd hM
  change Nat.card (Subgroup.center K) ∣ Nat.gcd m (2 ^ f + 1) * 1 at hdvd
  rw [mul_one] at hdvd
  have h3g : 3 ∣ Nat.gcd m (2 ^ f + 1) := h3.trans hdvd
  have hm3dvd : 3 ∣ m := h3g.trans (Nat.gcd_dvd_left _ _)
  have hadd : 3 ∣ 2 ^ f + 1 := h3g.trans (Nat.gcd_dvd_right _ _)
  have hfodd : Odd f := by
    rw [← Nat.not_even_iff_odd]
    exact fun heven => uc22p20v_not_three_dvd_add_one heven hadd
  have hm6 : ¬ 6 ≤ m := by
    intro hm6
    obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := LieModel.statedClassicalModel_of_ne_zero (by omega) hM
    have h1 := four_le_pRank_projSU_of_dvd_add (L := K') (n := m) (q := 2 ^ f) hK'
      (by omega) hadd
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e] at h1
    omega
  have hm_eq : m = 3 := by
    obtain ⟨k, hk⟩ := hm3dvd
    omega
  exact ⟨hm_eq, hfodd⟩


theorem k_ThreeCentralRankTwo_holds : K_ThreeCentralRankTwo := by
  have := CFSG.Adapters.certificate43_holds
  have hN := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20r_nativeGriess
  intro K _ _ t m f hadm hM hq hodd h3 hprank
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3Q := CFSG.SectionRank.pRank_quotient_le_three (p := 3) (by norm_num) hprank
    (Subgroup.center K) le_rfl
  cases t with
  | PSL => exact Or.inl ⟨rfl, psl_K01 hN K hadm hM hq hodd h3 h3Q⟩
  | PSU => exact Or.inr ⟨rfl, psu_K01 hN K hadm hM hq hodd h3 h3Q⟩
  | E6 =>
    obtain ⟨-, ⟨⟨-, -, -⟩, hm⟩⟩ := uc22p20v_exc_model hM (by decide)
    have h1 := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (by simp) hm
    omega
  | twistedE6 =>
    obtain ⟨-, ⟨⟨-, hf, -⟩, hm⟩⟩ := uc22p20v_exc_model hM (by decide)
    have h1 := CFSG.SectionRank.four_le_pRank_three_of_twistedE6Model_two hf hm
    omega
  | PSp => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | POmegaOdd => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | POmegaPlus => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | POmegaMinus => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | G2 => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | F4 => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | E7 => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | E8 => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | trialityD4 => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | twistedB2 => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | twistedG2 => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | twistedF4 => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim
  | Tits => exact (oddFree_K01 hN K hadm hM hq hodd h3 (by decide)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
