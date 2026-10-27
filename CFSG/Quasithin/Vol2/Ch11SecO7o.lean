module

public import CFSG.Quasithin.Vol2.Ch11SecO7g
public import CFSG.Quasithin.Vol2.Ch11SecO7c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

theorem two_pow_le_of_dvd {q A : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (h : 2 ^ (A + 1) ∣ q ^ 2 - 1) :
    2 ^ A ≤ q + 1 := by
  obtain ⟨k, rfl⟩ := hq
  have hk : 1 ≤ k := by omega
  have e : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := Nat.sub_eq_of_eq_add (by ring)
  rw [e] at h
  rcases A with _ | A
  · simp
  · have h1 : 2 ^ A ∣ k * (k + 1) := by
      rw [show 2 ^ (A + 1 + 1) = 4 * 2 ^ A by ring] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    rcases Nat.even_or_odd k with he | ho
    · have hc : Nat.Coprime (2 ^ A) (k + 1) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr he.add_one)
      have h2 := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h1)
      rw [pow_succ]
      omega
    · have hc : Nat.Coprime (2 ^ A) k := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ho)
      have h2 := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left h1)
      rw [pow_succ]
      omega

theorem ne_of_artin {A u c q : ℕ} (hA : 3 ≤ A) (hu : Odd u) (hlt : 4 * u < (2 ^ A) ^ 2)
    (hc : Odd c) (hq : Odd q) (hq3 : 3 ≤ q) : 2 ^ A * u * 2 ≠ c * (q * (q ^ 2 - 1)) := by
  intro h
  have hq9 : 9 ≤ q ^ 2 := by nlinarith
  have hq0 : q ^ 2 - 1 ≠ 0 := by omega
  obtain ⟨w, v, hv, hwv⟩ := Nat.exists_eq_two_pow_mul_odd hq0
  have h1 : 2 ^ (A + 1) * u = 2 ^ w * (c * q * v) := by
    calc 2 ^ (A + 1) * u = 2 ^ A * u * 2 := by ring
      _ = c * (q * (q ^ 2 - 1)) := h
      _ = 2 ^ w * (c * q * v) := by rw [hwv]; ring
  have hw : A + 1 = w := SecA.eq_of_two_pow_mul_odd hu ((hc.mul hq).mul hv) h1
  have hdvd : 2 ^ (A + 1) ∣ q ^ 2 - 1 := by
    rw [hwv, hw]
    exact dvd_mul_right _ _
  have hqA := two_pow_le_of_dvd hq hq3 hdvd
  obtain ⟨T, hT⟩ : ∃ T, 2 ^ A = 2 * T := ⟨2 ^ (A - 1), by
    rw [← pow_succ']
    congr 1
    omega⟩
  have hT4 : 4 ≤ T := by
    have : 2 ^ 3 ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hA
    omega
  rw [hT] at hlt hqA h
  have hcq : q * (q ^ 2 - 1) ≤ c * (q * (q ^ 2 - 1)) := Nat.le_mul_of_pos_left _ hc.pos
  have h2 : (2 * T - 1) * ((2 * T - 1) ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
    cube_sub_le (by omega) (by omega)
  have e : (2 * T - 1) * ((2 * T - 1) ^ 2 - 1) = 4 * T * ((2 * T - 1) * (T - 1)) := by
    zify [show 1 ≤ 2 * T by omega, show 1 ≤ T by omega,
      Nat.one_le_pow 2 (2 * T - 1) (by omega)]
    ring
  rw [e] at h2
  have h3 : T * T ≤ (2 * T - 1) * (T - 1) := by
    have hT4' : (4 : ℤ) ≤ T := by exact_mod_cast hT4
    zify [show 1 ≤ 2 * T by omega, show 1 ≤ T by omega]
    nlinarith
  obtain ⟨P, hP⟩ : ∃ P, P = (2 * T - 1) * (T - 1) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = q * (q ^ 2 - 1) := ⟨_, rfl⟩
  rw [← hP] at h2 h3
  rw [← hQ] at h2 hcq h
  have hsq : (2 * T) ^ 2 = 4 * (T * T) := by ring
  rw [hsq] at hlt
  have h6 : u + 1 ≤ P := by omega
  have h7 : 4 * T * (u + 1) ≤ 4 * T * P := Nat.mul_le_mul_left _ h6
  nlinarith

theorem l2two_ne_profile {A u : ℕ} (hu : Odd u) (hlt : 4 * u < (2 ^ A) ^ 2) (m : ℕ) :
    2 ^ m * ((2 ^ m) ^ 2 - 1) ≠ 2 ^ A * u := by
  intro h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hpos : 0 < 2 ^ A * u := Nat.mul_pos (by positivity) hu.pos
    rw [← h] at hpos
    simp at hpos
  · obtain ⟨hmA, hx⟩ := match_two (j := 1) (odd_pow m 2 hm (by norm_num)) hu (by simpa using h)
    rw [mul_one] at hmA
    subst hmA
    have h2m : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h4 : 4 ≤ (2 ^ m) ^ 2 := by nlinarith
    omega

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
