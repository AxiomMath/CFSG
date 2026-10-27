module

public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Timmesfeld.Bang

private theorem not_dvd_two_pow_pow_sub_pow {b c k i ℓ : ℕ} (hℓ : ℓ.Prime) (hb : 1 ≤ b)
    (hord : orderOf (2 : ZMod ℓ) = c * b) (hik : i < k) (hk : k < c) :
    ¬ ℓ ∣ (2 ^ b) ^ k - (2 ^ b) ^ i := by
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h0 : (2 : ZMod 2) = 0 := rfl
    rw [h0, orderOf_zero] at hord
    have : 0 < c * b := Nat.mul_pos (by omega) hb
    omega
  have hsplit : (2 ^ b) ^ k - (2 ^ b) ^ i = (2 ^ b) ^ i * (2 ^ (b * (k - i)) - 1) := by
    rw [Nat.mul_sub_one, pow_mul, ← pow_add, Nat.add_sub_of_le hik.le]
  rw [hsplit]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hℓ).1 hdvd with h1 | h1
  · rw [← pow_mul] at h1
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h1))
  · have h2 := orderOf_dvd_of_pow_eq_one ((dvd_two_pow_sub_one_iff _).1 h1)
    rw [hord, mul_comm b] at h2
    have h3 : c ∣ k - i := Nat.dvd_of_mul_dvd_mul_right (by omega) h2
    have := Nat.le_of_dvd (by omega) h3
    omega

theorem not_dvd_card_GL_of_orderOf_two_eq_mul {K : Type} [Field K] [Finite K] {b c k ℓ : ℕ}
    (hK : Nat.card K = 2 ^ b) (hb : 1 ≤ b) (hℓ : ℓ.Prime)
    (hord : orderOf (2 : ZMod ℓ) = c * b) (hk : k < c) :
    ¬ ℓ ∣ Nat.card (GL (Fin k) K) := by
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK]
  intro hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hℓ.prime _).1 hdvd
  exact not_dvd_two_pow_pow_sub_pow hℓ hb hord i.2 hk hi

end CFSG.Timmesfeld.Bang
