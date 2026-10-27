module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoShapeCard

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)

private theorem w183b5_card_PSL_three (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {p f : ℕ} (h : LieModel X .PSL 3 p f) :
    Nat.card X * Nat.gcd 3 (p ^ f - 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) := by
  obtain ⟨-, hM, -⟩ := hO X .PSL 3 p f h.admissible h
  simpa [lieOrderDivisor, lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide,
    Finset.prod_pair] using hM

private theorem w183b5_card_PSU_three (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {p f : ℕ} (h : LieModel X .PSU 3 p f) :
    Nat.card X * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  obtain ⟨-, hM, -⟩ := hO X .PSU 3 p f h.admissible h
  have h2 : Even (2 : ℕ) := by decide
  have h3 : ¬ Even (3 : ℕ) := by decide
  simpa [lieOrderDivisor, lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide,
    Finset.prod_pair, h2, h3] using hM

private theorem w183b5_psl_numer_ge (p : ℕ) (hp11 : 11 ≤ p) :
    14040000 < p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
  have h3 : 11 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp11 3
  have h2 : 11 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp11 2
  have hs2 : 11 ^ 2 - 1 ≤ p ^ 2 - 1 := Nat.sub_le_sub_right h2 1
  have hs3 : 11 ^ 3 - 1 ≤ p ^ 3 - 1 := Nat.sub_le_sub_right h3 1
  have hmul : 11 ^ 3 * ((11 ^ 2 - 1) * (11 ^ 3 - 1)) ≤
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul hs2 hs3)
  exact lt_of_lt_of_le (by norm_num) hmul

private theorem w183b5_psu_numer_ge (p : ℕ) (hp11 : 11 ≤ p) :
    14040000 < p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  have h3 : 11 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp11 3
  have h2 : 11 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp11 2
  have hs2 : 11 ^ 2 - 1 ≤ p ^ 2 - 1 := Nat.sub_le_sub_right h2 1
  have hs3 : 11 ^ 3 + 1 ≤ p ^ 3 + 1 := Nat.add_le_add_right h3 1
  have hmul : 11 ^ 3 * ((11 ^ 2 - 1) * (11 ^ 3 + 1)) ≤
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul hs2 hs3)
  exact lt_of_lt_of_le (by norm_num) hmul

private theorem w183b5_psl_gt {X : Type} [Group X] {p : ℕ} (hp11 : 11 ≤ p)
    (hM : Nat.card X * Nat.gcd 3 (p - 1) = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1))) :
    4680000 < Nat.card X := by
  have hdle : Nat.gcd 3 (p - 1) ≤ 3 := Nat.gcd_le_left (p - 1) (by norm_num)
  have hmul : Nat.card X * Nat.gcd 3 (p - 1) ≤ Nat.card X * 3 :=
    Nat.mul_le_mul_left (Nat.card X) hdle
  rw [hM] at hmul
  have hN := w183b5_psl_numer_ge p hp11
  have : 14040000 < Nat.card X * 3 := lt_of_lt_of_le hN hmul
  omega

private theorem w183b5_psu_gt {X : Type} [Group X] {p : ℕ} (hp11 : 11 ≤ p)
    (hM : Nat.card X * Nat.gcd 3 (p + 1) = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) :
    4680000 < Nat.card X := by
  have hdle : Nat.gcd 3 (p + 1) ≤ 3 := Nat.gcd_le_left (p + 1) (by norm_num)
  have hmul : Nat.card X * Nat.gcd 3 (p + 1) ≤ Nat.card X * 3 :=
    Nat.mul_le_mul_left (Nat.card X) hdle
  rw [hM] at hmul
  have hN := w183b5_psu_numer_ge p hp11
  have : 14040000 < Nat.card X * 3 := lt_of_lt_of_le hN hmul
  omega

private theorem w183b5_le_of_tail1812 {n : ℕ} (hc : Tail1812Orders n) : n ≤ 4680000 := by
  unfold Tail1812Orders at hc
  rcases hc with h | h | h | h | h | h | h <;> omega

theorem false_of_isL3_one_card_mem (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : IsL3 X 1) (hc : Tail1812Orders (Nat.card X)) : False := by
  have hM := w183b5_card_PSL_three hO h
  have hd : Nat.gcd 3 (2 ^ 1 - 1) = 1 := by decide
  have hn : (2 ^ 1) ^ 3 * (((2 ^ 1) ^ 2 - 1) * ((2 ^ 1) ^ 3 - 1)) = 168 := by norm_num
  rw [hd, hn, mul_one] at hM
  rw [hM] at hc
  exact absurd hc (by unfold Tail1812Orders; decide)

theorem false_of_isL3_two_card_mem (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : IsL3 X 2) (hc : Tail1812Orders (Nat.card X)) : False := by
  have hM := w183b5_card_PSL_three hO h
  have hd : Nat.gcd 3 (2 ^ 2 - 1) = 3 := by decide
  have hn : (2 ^ 2) ^ 3 * (((2 ^ 2) ^ 2 - 1) * ((2 ^ 2) ^ 3 - 1)) = 60480 := by norm_num
  rw [hd, hn] at hM
  have hcard : Nat.card X = 20160 := by omega
  rw [hcard] at hc
  exact absurd hc (by unfold Tail1812Orders; decide)

theorem false_of_psl_three_card_mem (hO : LieOrderFormulasInput) {X : Type} [Group X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : LieModel X .PSL 3 p 1)
    (hc : Tail1812Orders (Nat.card X)) : False := by
  have hM := w183b5_card_PSL_three hO h
  simp only [pow_one] at hM
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  rcases lt_or_ge p 11 with hp11 | hp11
  · interval_cases p
    · have hd : Nat.gcd 3 (3 - 1) = 1 := by decide
      have hn : 3 ^ 3 * ((3 ^ 2 - 1) * (3 ^ 3 - 1)) = 5616 := by norm_num
      rw [hd, hn, mul_one] at hM
      rw [hM] at hc
      exact absurd hc (by unfold Tail1812Orders; decide)
    · exact absurd hp (by norm_num)
    · have hd : Nat.gcd 3 (5 - 1) = 1 := by decide
      have hn : 5 ^ 3 * ((5 ^ 2 - 1) * (5 ^ 3 - 1)) = 372000 := by norm_num
      rw [hd, hn, mul_one] at hM
      rw [hM] at hc
      exact absurd hc (by unfold Tail1812Orders; decide)
    · exact absurd hp (by norm_num)
    · have hd : Nat.gcd 3 (7 - 1) = 3 := by decide
      have hn : 7 ^ 3 * ((7 ^ 2 - 1) * (7 ^ 3 - 1)) = 5630688 := by norm_num
      rw [hd, hn] at hM
      have hcard : Nat.card X = 1876896 := by omega
      rw [hcard] at hc
      exact absurd hc (by unfold Tail1812Orders; decide)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
  · have hgt : 4680000 < Nat.card X := w183b5_psl_gt hp11 hM
    have hle : Nat.card X ≤ 4680000 := w183b5_le_of_tail1812 hc
    omega

theorem false_of_psu_three_card_mem (hO : LieOrderFormulasInput) {X : Type} [Group X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : LieModel X .PSU 3 p 1)
    (hc : Tail1812Orders (Nat.card X)) : False := by
  have hM := w183b5_card_PSU_three hO h
  simp only [pow_one] at hM
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  rcases lt_or_ge p 11 with hp11 | hp11
  · interval_cases p
    · have hd : Nat.gcd 3 (3 + 1) = 1 := by decide
      have hn : 3 ^ 3 * ((3 ^ 2 - 1) * (3 ^ 3 + 1)) = 6048 := by norm_num
      rw [hd, hn, mul_one] at hM
      rw [hM] at hc
      exact absurd hc (by unfold Tail1812Orders; decide)
    · exact absurd hp (by norm_num)
    · have hd : Nat.gcd 3 (5 + 1) = 3 := by decide
      have hn : 5 ^ 3 * ((5 ^ 2 - 1) * (5 ^ 3 + 1)) = 378000 := by norm_num
      rw [hd, hn] at hM
      have hcard : Nat.card X = 126000 := by omega
      rw [hcard] at hc
      exact absurd hc (by unfold Tail1812Orders; decide)
    · exact absurd hp (by norm_num)
    · have hd : Nat.gcd 3 (7 + 1) = 1 := by decide
      have hn : 7 ^ 3 * ((7 ^ 2 - 1) * (7 ^ 3 + 1)) = 5663616 := by norm_num
      rw [hd, hn, mul_one] at hM
      rw [hM] at hc
      exact absurd hc (by unfold Tail1812Orders; decide)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
  · have hgt : 4680000 < Nat.card X := w183b5_psu_gt hp11 hM
    have hle : Nat.card X ≤ 4680000 := w183b5_le_of_tail1812 hc
    omega

end CFSG.LocalAnalysis.WeakClosure81

end
