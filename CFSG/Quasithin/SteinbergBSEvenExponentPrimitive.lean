module

public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin.SteinbergBS

open CFSG.Timmesfeld

theorem orderOf_two_zmod_nine : orderOf (2 : ZMod 9) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun k hk hk0 => ?_⟩
  interval_cases k <;> decide

theorem orderOf_two_zmod_prime_ne_six {ℓ : ℕ} (hℓ : ℓ.Prime) : orderOf (2 : ZMod ℓ) ≠ 6 := by
  intro h6
  have h1 : (2 : ZMod ℓ) ^ 6 = 1 := by
    rw [← h6]
    exact pow_orderOf_eq_one _
  have h2 : ℓ ∣ 3 ^ 2 * 7 := (Bang.dvd_two_pow_sub_one_iff 6).2 h1
  rcases (Nat.Prime.dvd_mul hℓ).1 h2 with h | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (hℓ.dvd_of_dvd_pow h)
    have h3 := orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 3) ^ 2 = 1)
    rw [h6] at h3
    omega
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ (by norm_num : Nat.Prime 7)).1 h
    have h3 := orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 7) ^ 3 = 1)
    rw [h6] at h3
    omega

theorem qrc_binary_even_exponent_primitive_divisor :
    (∀ m : ℕ, 2 ≤ m → Even m → m ≠ 6 →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf (2 : ZMod ℓ) = m ∧ ℓ ∣ 2 ^ (m / 2) + 1) ∧
    (∀ ℓ : ℕ, ℓ.Prime → orderOf (2 : ZMod ℓ) ≠ 6) ∧ orderOf (2 : ZMod 9) = 6 := by
  refine ⟨fun m hm hme hm6 => ?_, fun ℓ hℓ => orderOf_two_zmod_prime_ne_six hℓ,
    orderOf_two_zmod_nine⟩
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimitivePrimeDivisor hm hm6
  have hk : 0 < m := by omega
  have hpow : ∀ a : ℕ, (2 : ZMod ℓ) ^ a = 1 ↔ m ∣ a := fun a => by
    rw [← Bang.dvd_two_pow_sub_one_iff]
    exact hℓ.dvd_sub_one_iff hk a
  have hord : orderOf (2 : ZMod ℓ) = m :=
    Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((hpow _).2 dvd_rfl))
      ((hpow _).1 (pow_orderOf_eq_one _))
  obtain ⟨j, hj⟩ := hme
  refine ⟨ℓ, hℓ.prime, hℓ.ne_two hk, hord, (hℓ.dvd_add_one_iff hk (m / 2)).2 ⟨⟨1, by omega⟩, ?_⟩⟩
  rintro ⟨c, hc⟩
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · omega
  · have h1 : m ≤ m * c := Nat.le_mul_of_pos_right _ hc0
    omega

end CFSG.Quasithin.SteinbergBS
