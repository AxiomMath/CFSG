module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

theorem three_le_prime_pow {p f : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f) :
    3 ≤ p ^ f := by
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  calc 3 ≤ p := h3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf

theorem gcd_succ_three_le (q : ℕ) : Nat.gcd (q + 1) 3 ≤ 3 :=
  Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _)

theorem gcd_succ_three_dvd (q : ℕ) : Nat.gcd (q + 1) 3 ∣ q + 1 := Nat.gcd_dvd_left _ _

theorem gcd_succ_three_pos (q : ℕ) : 0 < Nat.gcd (q + 1) 3 :=
  Nat.gcd_pos_of_pos_right _ (by norm_num)

theorem eq_one_of_pow_eq_sq {q s n t d : ℕ} (hq : 3 ≤ q) (hd : d ≤ 3) (hs : s ^ n = q ^ 2)
    (ht : t * d = q ^ 2 - 1) (hdvd : t ∣ s - 1) : n = 1 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp only [pow_zero] at hs
      nlinarith
    · rfl
  · exfalso
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · subst h0
        rw [zero_pow (by omega)] at hs
        nlinarith
      · exact h0
    have hsq : s ^ 2 ≤ q ^ 2 := hs ▸ Nat.pow_le_pow_right hs1 hn
    have hsq' : s ≤ q := (Nat.pow_le_pow_iff_left (by norm_num)).mp hsq
    have hs2 : 2 ≤ s := by
      by_contra h
      have : s = 1 := by omega
      subst this
      simp only [one_pow] at hs
      nlinarith
    have hts : t ≤ s - 1 := Nat.le_of_dvd (by omega) hdvd
    have hq2 : q ^ 2 - 1 ≤ 3 * (q - 1) := by
      rw [← ht]
      calc t * d ≤ (s - 1) * 3 := Nat.mul_le_mul hts hd
        _ ≤ 3 * (q - 1) := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have : q ^ 2 = q * q := sq q
    have h9 : 3 * q ≤ q * q := Nat.mul_le_mul_right q hq
    omega

theorem eq_five_of_pow_eq_sq {p f s m w : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hs : s ^ m = (p ^ f) ^ 2) (hm : 2 ≤ m) (hw : w * Nat.gcd (p ^ f + 1) 3 = p ^ f + 1)
    (hdvd : w ∣ s - 1) : p = 5 ∧ f = 1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hsd : s ∣ p ^ (2 * f) := by
    rw [mul_comm, pow_mul, ← hs]
    exact dvd_pow_self s (by omega)
  obtain ⟨e, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hsd
  have hem : e * m = 2 * f := by
    have : p ^ (e * m) = p ^ (2 * f) := by rw [pow_mul, hs, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective hp.two_le this
  have hd3 := gcd_succ_three_le (p ^ f)
  have hd0 := gcd_succ_three_pos (p ^ f)
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; omega
    · exact h
  have hpe : 3 ≤ p ^ e := three_le_prime_pow hp hpodd he1
  have hwle : w ≤ p ^ e - 1 := Nat.le_of_dvd (by omega) hdvd
  rcases Nat.eq_or_lt_of_le hm with hm2 | hm3
  · subst hm2
    have hef : e = f := by omega
    subst hef
    have h2 : w ∣ 2 := by
      have h1 : w ∣ p ^ e + 1 := ⟨_, hw.symm⟩
      have := Nat.dvd_sub h1 hdvd
      rwa [show p ^ e + 1 - (p ^ e - 1) = 2 by omega] at this
    have hw2 : w ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hq5 : p ^ e ≤ 5 := by
      have : w * Nat.gcd (p ^ e + 1) 3 ≤ 2 * 3 := Nat.mul_le_mul hw2 hd3
      omega
    have he : e = 1 := by
      by_contra hne
      have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
      nlinarith
    subst he
    rw [pow_one] at hq5 hw
    refine ⟨?_, rfl⟩
    interval_cases p
    · norm_num at hw
      omega
    · exact absurd hp (by norm_num)
    · rfl
  · exfalso
    have hef : e < f := by
      have : 3 * e ≤ e * m := by rw [Nat.mul_comm e m]; exact Nat.mul_le_mul_right e hm3
      omega
    have hq : 3 * p ^ e ≤ p ^ f := by
      calc 3 * p ^ e ≤ p * p ^ e := Nat.mul_le_mul_right _ hp3
        _ = p ^ (e + 1) := by rw [pow_succ, mul_comm]
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hef
    have : w * Nat.gcd (p ^ f + 1) 3 ≤ (p ^ e - 1) * 3 := Nat.mul_le_mul hwle hd3
    omega

theorem gcd_sq_sub_one_two_mul_sub_one (q : ℕ) (hq : 1 ≤ q) :
    Nat.gcd (q ^ 2 - 1) (2 * q - 1) = Nat.gcd (q + 1) 3 := by
  have e1 : (2 * q - 1) * (2 * q + 1) = 4 * (q ^ 2 - 1) + 3 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    have h1 : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
    rw [h1, Nat.add_sub_cancel, show 2 * (r + 1) - 1 = 2 * r + 1 by omega]
    ring
  have hg3 : Nat.gcd (q ^ 2 - 1) (2 * q - 1) ∣ 3 := by
    have h1 : Nat.gcd (q ^ 2 - 1) (2 * q - 1) ∣ (2 * q - 1) * (2 * q + 1) :=
      Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _
    have h2 : Nat.gcd (q ^ 2 - 1) (2 * q - 1) ∣ 4 * (q ^ 2 - 1) :=
      Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) _
    rw [e1] at h1
    exact (Nat.dvd_add_right h2).mp h1
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    have h1 : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
    rw [h1, Nat.add_sub_cancel, Nat.add_sub_cancel]
    ring
  by_cases h3 : 3 ∣ q + 1
  · rw [Nat.gcd_eq_right h3]
    apply Nat.dvd_antisymm hg3
    apply Nat.dvd_gcd
    · rw [hsq]; exact Dvd.dvd.mul_left h3 _
    · omega
  · have hd : Nat.gcd (q + 1) 3 = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_right (q + 1) 3) with h | h
      · exact h
      · exact absurd (h ▸ Nat.gcd_dvd_left (q + 1) 3) h3
    rw [hd]
    rcases (Nat.dvd_prime Nat.prime_three).mp hg3 with h | h
    · exact h
    · exfalso
      have : 3 ∣ 2 * q - 1 := h ▸ Nat.gcd_dvd_right _ _
      omega

end CFSG.UnitaryThreeRecognition.Heisenberg
