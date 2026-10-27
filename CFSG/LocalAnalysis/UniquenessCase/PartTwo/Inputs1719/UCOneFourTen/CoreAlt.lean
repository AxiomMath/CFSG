module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelOvergroupHolds
import CFSG.LocalAnalysis.OddStandard.GlueAlt
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Target

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem coreAltSlice : CoreAltSlice := by
  intro X _ _ K L T Y n m h ⟨e⟩
  obtain ⟨hoddn, hn3⟩ := h.odd_three_le
  obtain ⟨a, rfl⟩ := hoddn
  have ha1 : 1 ≤ a := by omega
  have hcard : Nat.card (Bar2 L) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.card_of_isSz_two_pow h.sz
  have hN : Nat.card (↥K ⧸ center ↥K) =
      Nat.card ↥(alternatingGroup (Fin m)) :=
    Nat.card_congr e.toEquiv
  have hbar : Nat.card (Bar2 L) ∣ Nat.card ↥(alternatingGroup (Fin m)) := by
    rw [← hN]
    exact h.card_bar2_dvd_card_quotient_center
  have h64bar : 2 ^ 6 ∣ Nat.card (Bar2 L) := by
    rw [hcard]
    have h : 2 ^ 6 ∣ (2 ^ (2 * a + 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  have hm2 : 2 ≤ m := by
    by_contra hm
    have hm1 : m ≤ 1 := by omega
    have hA1 : Nat.card ↥(alternatingGroup (Fin m)) = 1 := by
      have h2 : Nat.card (Fin m) ≤ 2 := by
        rw [Nat.card_fin]
        omega
      have hbot : alternatingGroup (Fin m) = ⊥ :=
        alternatingGroup.eq_bot_of_card_le_two h2
      rw [hbot]
      simp
    have h64A : 2 ^ 6 ∣ Nat.card ↥(alternatingGroup (Fin m)) := h64bar.trans hbar
    rw [hA1] at h64A
    norm_num at h64A
  have h2A : 2 * Nat.card ↥(alternatingGroup (Fin m)) = m.factorial := by
    have hnt : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm2
    have h := @two_mul_card_alternatingGroup (Fin m) inferInstance inferInstance hnt
    rw [Nat.card_eq_fintype_card, h, Fintype.card_perm, Fintype.card_fin]
  have h2bar : 2 * Nat.card (Bar2 L) ∣ m.factorial := by
    rw [← h2A]
    exact Nat.mul_dvd_mul_left 2 hbar
  have hm13 : 13 ≤ m := by
    by_contra hm13
    have hm12 : m ≤ 12 := by omega
    have h2bar12 : 2 * Nat.card (Bar2 L) ∣ Nat.factorial 12 :=
      h2bar.trans (Nat.factorial_dvd_factorial hm12)
    by_cases ha : a = 1
    · subst ha
      have h13bar : 13 ∣ Nat.card (Bar2 L) := by
        rw [hcard]
        norm_num
      have h13fact : 13 ∣ Nat.factorial 12 :=
        (dvd_mul_of_dvd_right h13bar 2).trans h2bar12
      have h13le : 13 ≤ 12 :=
        (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 13)).1 h13fact
      omega
    · have ha2 : 2 ≤ a := by omega
      have h210bar : 2 ^ 10 ∣ Nat.card (Bar2 L) := by
        rw [hcard]
        have h : 2 ^ 10 ∣ (2 ^ (2 * a + 1)) ^ 2 := by
          rw [← pow_mul]
          exact pow_dvd_pow 2 (by omega)
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
      have h211bar : 2 ^ 11 ∣ 2 * Nat.card (Bar2 L) := by
        rw [show (2 : ℕ) ^ 11 = 2 * 2 ^ 10 by norm_num]
        exact Nat.mul_dvd_mul_left 2 h210bar
      have h211fact : 2 ^ 11 ∣ Nat.factorial 12 := h211bar.trans h2bar12
      have hnot : ¬ (2 ^ 11 ∣ Nat.factorial 12) := by decide
      exact hnot h211fact
  have hm8 : 8 ≤ m := by omega
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr h.quasisimple.1
  have hZle : Nat.card ↥(center ↥K) ≤ 2 :=
    @CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt ↥K inferInstance inferInstance
      hperf m hm8 e
  have hZodd : Odd (Nat.card ↥(center ↥K)) := h.odd_card_center
  have hZ1 : Nat.card ↥(center ↥K) = 1 := by
    obtain ⟨k, hk⟩ := hZodd
    omega
  have hcenter : center ↥K = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  have e' : ↥K ≃* ↥(alternatingGroup (Fin m)) :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientBot (G := ↥K))).symm.trans e
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
    CFSG.AGLEmbedding.le_pRank_of_mulEquiv_alternatingGroup (k := 4) e' (by omega)
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 :=
    h.pRank_K_le (p := 3) Nat.prime_three (by norm_num)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
