module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.RankThree.PartOne.KFOUT3

theorem prod_pow_sub_eq (q : ℕ) (hq : 2 ≤ q) :
    ∏ i : Fin 3, (q ^ 3 - q ^ (i : ℕ)) = (q - 1) * ((q ^ 3 - 1) * q ^ 3 * (q ^ 2 - 1)) := by
  rw [Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have h1 : 1 ≤ q := by omega
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : q ^ 2 ≤ q ^ 3 := by nlinarith
  have h4 : 1 ≤ q ^ 2 := by nlinarith
  have h5 : 1 ≤ q ^ 3 := by nlinarith
  have h6 : q ≤ q ^ 3 := by nlinarith
  zify [h1, h2, h3, h4, h5, h6]
  ring

variable {K : Type} [Field K]

theorem card_SL3_eq [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      (Nat.card K ^ 3 - 1) * Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) := by
  have := Fintype.ofFinite K
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, prod_pow_sub_eq _ hq]
  exact Nat.mul_div_cancel_left _ (by omega)

theorem factorization_card_SL3 [Finite K] (hq : Nat.card K % 3 = 2) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 3) K)).factorization 3 =
      (Nat.card K ^ 2 - 1).factorization 3 := by
  have hq2 : 2 ≤ Nat.card K := by omega
  have h1 : ¬ 3 ∣ Nat.card K ^ 3 - 1 := by
    have h : Nat.card K ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hq]
    have : 1 ≤ Nat.card K ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have h2 : ¬ 3 ∣ Nat.card K := by omega
  have hpos1 : Nat.card K ^ 3 - 1 ≠ 0 := by
    have : 2 ^ 3 ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hq2 3
    omega
  have hpos2 : Nat.card K ^ 3 ≠ 0 := by positivity
  have hpos3 : Nat.card K ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  rw [card_SL3_eq, Nat.factorization_mul (mul_ne_zero hpos1 hpos2) hpos3,
    Nat.factorization_mul hpos1 hpos2]
  simp [Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd h2]

end CFSG.RankThree.PartOne.KFOUT3
