module

public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.GF2n.Smith81.SubCfg

open CFSG.Timmesfeld

theorem pow_sub_pow_eq {g n i : ℕ} (hi : i ≤ n) :
    (2 ^ g) ^ n - (2 ^ g) ^ i = (2 ^ g) ^ i * ((2 ^ g) ^ (n - i) - 1) := by
  rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi]

theorem not_dvd_prod_GL {r e g n : ℕ} (hr : IsPrimitivePrimeDivisor r e) (he : 0 < e)
    (hj : ∀ j, 1 ≤ j → j ≤ n → ¬ e ∣ g * j) :
    ¬ r ∣ ∏ i : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ)) := by
  intro hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hr.prime.prime _).mp hdvd
  rw [pow_sub_pow_eq (Nat.le_of_lt i.2)] at hi
  rcases (Nat.Prime.dvd_mul hr.prime).mp hi with h | h
  · rw [← pow_mul] at h
    have h2 : r ∣ 2 := hr.prime.dvd_of_dvd_pow h
    exact hr.ne_two he ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp h2)
  · rw [← pow_mul, hr.dvd_sub_one_iff he] at h
    exact hj (n - i) (by have := i.2; omega) (Nat.sub_le _ _) h

theorem e4_not_dvd {f g k : ℕ} (hf : 0 < f) (hk : g * k = 17 * f) (h17 : ¬ 17 ∣ k) :
    ∀ j, 1 ≤ j → j ≤ k - 1 → ¬ 6 * f ∣ g * j := by
  intro j hj1 hjk hdvd
  have h17g : 17 ∣ g := by
    have h1 : 17 ∣ g * k := hk ▸ dvd_mul_right 17 f
    exact ((Nat.Prime.dvd_mul (by norm_num)).mp h1).resolve_right h17
  obtain ⟨h, rfl⟩ := h17g
  have hfk : f = h * k := by
    have : 17 * (h * k) = 17 * f := by rw [← hk]; ring
    omega
  subst hfk
  have hh : 0 < h := Nat.pos_of_mul_pos_right hf
  have h1 : 6 * k ∣ 17 * j := by
    have h2 : h * (6 * k) ∣ h * (17 * j) := by
      have : 6 * (h * k) = h * (6 * k) := by ring
      have : 17 * h * j = h * (17 * j) := by ring
      rw [‹6 * (h * k) = _›, ‹17 * h * j = _›] at hdvd
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hh h2
  have hcop : Nat.Coprime (6 * k) 17 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    intro h6k
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h6k with h6 | h6
    · exact absurd h6 (by norm_num)
    · exact h17 h6
  have h3 : 6 * k ∣ j := hcop.dvd_of_dvd_mul_left h1
  have := Nat.le_of_dvd (by omega) h3
  omega

theorem e5_not_dvd {f g k : ℕ} (hf : 0 < f) (hk : g * k = 33 * f) (h11 : ¬ 11 ∣ k) :
    ∀ j, 1 ≤ j → j ≤ k - 1 → ¬ 10 * f ∣ g * j := by
  intro j hj1 hjk hdvd
  have h11g : 11 ∣ g := by
    have h1 : 11 ∣ g * k := by
      rw [hk]
      exact Dvd.dvd.mul_right (by norm_num) f
    exact ((Nat.Prime.dvd_mul (by norm_num)).mp h1).resolve_right h11
  obtain ⟨h, rfl⟩ := h11g
  have hfk : 3 * f = h * k := by
    have : 11 * (h * k) = 11 * (3 * f) := by rw [← mul_assoc 11 h k, hk]; ring
    omega
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0
      omega
    · exact h0
  have h1 : 10 * k ∣ 33 * j := by
    have h2 : h * (10 * k) ∣ h * (33 * j) := by
      have e1 : h * (10 * k) = 10 * (3 * f) := by rw [hfk]; ring
      have e2 : h * (33 * j) = 3 * (11 * h * j) := by ring
      rw [e1, e2, show 10 * (3 * f) = 3 * (10 * f) by ring]
      exact mul_dvd_mul_left 3 hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hh h2
  have hcop : Nat.Coprime (10 * k) 11 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    intro h10k
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h10k with h10 | h10
    · exact absurd h10 (by norm_num)
    · exact h11 h10
  have h3 : 10 * k ∣ 3 * j := by
    have : 33 * j = 11 * (3 * j) := by ring
    rw [this] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  have := Nat.le_of_dvd (by omega) h3
  omega

theorem e4_width_eq {f g m : ℕ} (hf : 0 < f) (h2 : g * (m * (m - 1)) = 12 * f)
    (hQ : g * (4 * m + 1) = 17 * f) : m = 4 ∧ g = f := by
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · subst h0
      omega
    · exact h0
  have key : 17 * (m * (m - 1)) = 12 * (4 * m + 1) := by
    have : g * (17 * (m * (m - 1))) = g * (12 * (4 * m + 1)) := by
      calc g * (17 * (m * (m - 1))) = 17 * (g * (m * (m - 1))) := by ring
        _ = 17 * (12 * f) := by rw [h2]
        _ = 12 * (17 * f) := by ring
        _ = 12 * (g * (4 * m + 1)) := by rw [hQ]
        _ = g * (12 * (4 * m + 1)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg this
  have hm : m = 4 := by
    rcases Nat.lt_or_ge m 5 with h5 | h5
    · interval_cases m <;> omega
    · have h1 : m - 1 ≥ 4 := by omega
      have h2' : m * (m - 1) ≥ m * 4 := Nat.mul_le_mul_left m h1
      nlinarith
  subst hm
  refine ⟨rfl, ?_⟩
  omega

theorem e5_no_width {f g m : ℕ} (hf : 0 < f) (h2 : g * (m * (m - 1)) = 30 * f)
    (hQ : g * (4 * m + 1) = 33 * f) : False := by
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · subst h0
      omega
    · exact h0
  have key : 11 * (m * (m - 1)) = 10 * (4 * m + 1) := by
    have : g * (33 * (m * (m - 1))) = g * (30 * (4 * m + 1)) := by
      calc g * (33 * (m * (m - 1))) = 33 * (g * (m * (m - 1))) := by ring
        _ = 33 * (30 * f) := by rw [h2]
        _ = 30 * (33 * f) := by ring
        _ = 30 * (g * (4 * m + 1)) := by rw [hQ]
        _ = g * (30 * (4 * m + 1)) := by ring
    have := Nat.eq_of_mul_eq_mul_left hg this
    omega
  rcases Nat.lt_or_ge m 6 with h6 | h6
  · interval_cases m <;> omega
  · have h1 : m - 1 ≥ 5 := by omega
    have h2' : m * (m - 1) ≥ m * 5 := Nat.mul_le_mul_left m h1
    nlinarith

theorem e4_seventeen_dvd {f g d N : ℕ} (hf : 2 ≤ f) (hQ : (2 ^ g) ^ (d + 1) = (2 ^ f) ^ 17)
    (hN : (2 ^ f) ^ 6 - 1 ∣ N) (hdvd : N ∣ ∏ i : Fin d, ((2 ^ g) ^ d - (2 ^ g) ^ (i : ℕ))) :
    17 ∣ d + 1 := by
  have hk : g * (d + 1) = 17 * f := by
    rw [← pow_mul, ← pow_mul] at hQ
    have := Nat.pow_right_injective (le_refl 2) hQ
    linarith
  by_contra h17
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 6 * f) (by omega) (by omega)
  have hr' : r ∣ (2 ^ f) ^ 6 - 1 := by
    rw [← pow_mul, mul_comm]
    exact hr.dvd
  exact not_dvd_prod_GL hr (by omega)
    (fun j hj1 hjd => e4_not_dvd (by omega) hk h17 j hj1 (by omega)) ((hr'.trans hN).trans hdvd)

theorem e5_eleven_dvd {f g d N : ℕ} (hf : 2 ≤ f) (hQ : (2 ^ g) ^ (d + 1) = (2 ^ f) ^ 33)
    (hN : (2 ^ f) ^ 10 - 1 ∣ N) (hdvd : N ∣ ∏ i : Fin d, ((2 ^ g) ^ d - (2 ^ g) ^ (i : ℕ))) :
    11 ∣ d + 1 := by
  have hk : g * (d + 1) = 33 * f := by
    rw [← pow_mul, ← pow_mul] at hQ
    have := Nat.pow_right_injective (le_refl 2) hQ
    linarith
  by_contra h11
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 10 * f) (by omega) (by omega)
  have hr' : r ∣ (2 ^ f) ^ 10 - 1 := by
    rw [← pow_mul, mul_comm]
    exact hr.dvd
  exact not_dvd_prod_GL hr (by omega)
    (fun j hj1 hjd => e5_not_dvd (by omega) hk h11 j hj1 (by omega)) ((hr'.trans hN).trans hdvd)

end CFSG.RankThree.GF2n.Smith81.SubCfg
