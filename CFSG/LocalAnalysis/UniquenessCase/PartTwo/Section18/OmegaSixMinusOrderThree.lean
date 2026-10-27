module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixed
public import CFSG.LieType.Universal.Spin.Forms

import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus)

private lemma two_pow_even_mod_three_T2J9c {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h4 : (2 : ℕ) ^ 2 ≡ 1 [MOD 3] := by norm_num [Nat.ModEq]
  have h : (2 : ℕ) ^ (m + m) ≡ 1 [MOD 3] := by
    rw [show m + m = 2 * m by omega, pow_mul]
    simpa using Nat.ModEq.pow m h4
  rw [Nat.ModEq] at h
  norm_num at h
  exact h

private lemma modEq_one_of_mod_three_T2J9c {q : ℕ} (h3 : q % 3 = 1) : q ≡ 1 [MOD 3] := by
  show q % 3 = 1 % 3
  rw [h3]

private lemma not_three_dvd_of_modEq_one_T2J9c {a : ℕ} (h : a ≡ 1 [MOD 3]) : ¬ 3 ∣ a := by
  rw [← Nat.modEq_zero_iff_dvd]
  intro h0
  have h2 : (0 : ℕ) % 3 = (1 : ℕ) % 3 := h0.symm.trans h
  norm_num at h2

private lemma not_three_dvd_of_modEq_two_T2J9c {a : ℕ} (h : a ≡ 2 [MOD 3]) : ¬ 3 ∣ a := by
  rw [← Nat.modEq_zero_iff_dvd]
  intro h0
  have h2 : (0 : ℕ) % 3 = (2 : ℕ) % 3 := h0.symm.trans h
  norm_num at h2

private lemma factorization_three_q_sq_sub_one_T2J9c {q : ℕ} (hq : 2 ≤ q) (h3 : q % 3 = 1) :
    (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 := by
  have hq1 : q - 1 ≠ 0 := by omega
  have hq1mod : q + 1 ≡ 2 [MOD 3] := by
    have h := Nat.ModEq.add_right 1 (modEq_one_of_mod_three_T2J9c h3)
    simpa using h
  have hc1 : ¬ 3 ∣ q + 1 := not_three_dvd_of_modEq_two_T2J9c hq1mod
  have hBeq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    simpa using Nat.sq_sub_sq q 1
  rw [hBeq, Nat.factorization_mul (by omega : q + 1 ≠ 0) hq1]
  simp [Nat.factorization_eq_zero_of_not_dvd hc1]

private lemma factorization_three_q_pow_four_sub_one_T2J9c {q : ℕ} (hq : 2 ≤ q)
    (h3 : q % 3 = 1) :
    (q ^ 4 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 := by
  have hq2 : q ^ 2 - 1 ≠ 0 := by
    have h := pow_le_pow_left' hq 2
    norm_num at h
    omega
  have hq2mod : q ^ 2 + 1 ≡ 2 [MOD 3] := by
    have h := Nat.ModEq.add_right 1 (Nat.ModEq.pow 2 (modEq_one_of_mod_three_T2J9c h3))
    simpa using h
  have hc2 : ¬ 3 ∣ q ^ 2 + 1 := not_three_dvd_of_modEq_two_T2J9c hq2mod
  have hsq : (q ^ 2) ^ 2 = q ^ 4 := by rw [← pow_mul]
  have hDeq : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
    have h := Nat.sq_sub_sq (q ^ 2) 1
    simpa [hsq] using h
  rw [hDeq, Nat.factorization_mul (by omega : q ^ 2 + 1 ≠ 0) hq2]
  simp [Nat.factorization_eq_zero_of_not_dvd hc2]

private lemma factorization_three_q_pow_six_T2J9c {q : ℕ} (h3 : q % 3 = 1) :
    (q ^ 6).factorization 3 = 0 := by
  have hq6mod : q ^ 6 ≡ 1 [MOD 3] := by
    simpa using Nat.ModEq.pow 6 (modEq_one_of_mod_three_T2J9c h3)
  exact Nat.factorization_eq_zero_of_not_dvd (not_three_dvd_of_modEq_one_T2J9c hq6mod)

private lemma factorization_three_q_cube_add_one_T2J9c {q : ℕ} (h3 : q % 3 = 1) :
    (q ^ 3 + 1).factorization 3 = 0 := by
  have hq3mod : q ^ 3 + 1 ≡ 2 [MOD 3] := by
    have h := Nat.ModEq.add_right 1 (Nat.ModEq.pow 3 (modEq_one_of_mod_three_T2J9c h3))
    simpa using h
  exact Nat.factorization_eq_zero_of_not_dvd (not_three_dvd_of_modEq_two_T2J9c hq3mod)

private lemma factorization_three_ordSU_four_T2J9c {q : ℕ} (hq : 2 ≤ q) (h3 : q % 3 = 1) :
    (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))).factorization 3 =
      2 * (q - 1).factorization 3 := by
  have hq0 : q ≠ 0 := by omega
  have hB : q ^ 2 - 1 ≠ 0 := by
    have h := pow_le_pow_left' hq 2
    norm_num at h
    omega
  have hC : q ^ 3 + 1 ≠ 0 := by omega
  have hD : q ^ 4 - 1 ≠ 0 := by
    have h := pow_le_pow_left' hq 4
    norm_num at h
    omega
  have hA : q ^ 6 ≠ 0 := pow_ne_zero _ hq0
  have hDz := factorization_three_q_pow_four_sub_one_T2J9c hq h3
  have hBz := factorization_three_q_sq_sub_one_T2J9c hq h3
  have hq6z := factorization_three_q_pow_six_T2J9c h3
  have hq3z := factorization_three_q_cube_add_one_T2J9c h3
  have h1 : (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))).factorization 3
      = (q ^ 6).factorization 3
        + (((q ^ 2 - 1).factorization 3 + (q ^ 3 + 1).factorization 3)
          + (q ^ 4 - 1).factorization 3) := by
    rw [Nat.factorization_mul hA (mul_ne_zero (mul_ne_zero hB hC) hD),
        Nat.factorization_mul (mul_ne_zero hB hC) hD,
        Nat.factorization_mul hB hC]
    simp only [Finsupp.add_apply]
  rw [h1, hq6z, hq3z, hDz, hBz]
  omega

theorem factorization_three_natCard_gom_quadMinus_three {F : Type} [Field F] [Finite F]
    [CharP F 2] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : Even n) :
    (Nat.card (Gom (quadMinus 3 F b c))).factorization 3 =
      2 * (Nat.card F - 1).factorization 3 := by
  have hcardGom : Nat.card (Gom (quadMinus 3 F b c)) =
      CFSG.SeitzReduction.F4Pilot.ordSU 4 (Nat.card F) := by
    rw [← Nat.card_congr
      (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr).toEquiv]
    exact CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_three (K := F) hirr
  rw [hcardGom, CFSG.SeitzReduction.F4Pilot.ordSU_four]
  refine factorization_three_ordSU_four_T2J9c (q := Nat.card F) ?_ ?_
  · have h := Finite.one_lt_card (α := F)
    omega
  · rw [hcard]
    exact two_pow_even_mod_three_T2J9c hn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
