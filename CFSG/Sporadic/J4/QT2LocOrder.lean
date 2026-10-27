module

public import CFSG.Sporadic.J4

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4

theorem card_J_factored :
    Nat.card J = 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 := by
  rw [card_J j4Facts]
  norm_num

theorem not_twentyfive_dvd_card_J : ¬ 25 ∣ Nat.card J := by
  rw [card_J j4Facts]
  norm_num

theorem card_J_factorization_five :
    (Nat.card J).factorization 5 = 1 := by
  rw [card_J_factored]
  have h : (2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 : ℕ) = 5 * (2 ^ 21 *
      3 ^ 3 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43) := by ring
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply]
  have h5 : (5 : ℕ).factorization 5 = 1 := Nat.Prime.factorization_self (by norm_num)
  have h0 : (2 ^ 21 * 3 ^ 3 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 : ℕ).factorization 5 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h5, h0]

end CFSG.Sporadic.J4.QT2
