module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.SzArith

private theorem not_dvd_A_of_dvd_succ {ℓ r : ℕ} (hℓ : ℓ.Prime) (hA : ℓ ∣ r ^ 2 + 3 * r + 3)
    (h : ℓ ∣ r + 1) : False := by
  have h1 : ℓ ∣ (r + 1) * (r + 2) := Dvd.dvd.mul_right h _
  have h2 : r ^ 2 + 3 * r + 3 = (r + 1) * (r + 2) + 1 := by ring
  rw [h2] at hA
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp hA))

private theorem not_dvd_A_of_dvd {ℓ r : ℕ} (hℓ : ℓ.Prime) (h3 : ¬ 3 ∣ r ^ 2 + 3 * r + 3)
    (hA : ℓ ∣ r ^ 2 + 3 * r + 3) (h : ℓ ∣ r) : False := by
  have h1 : ℓ ∣ r * (r + 3) := Dvd.dvd.mul_right h _
  have h2 : r ^ 2 + 3 * r + 3 = r * (r + 3) + 3 := by ring
  rw [h2] at hA
  have h4 : ℓ ∣ 3 := (Nat.dvd_add_right h1).mp hA
  have h5 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h4
  subst h5
  exact h3 (h2 ▸ hA)

private theorem not_dvd_A_of_dvd_sq {ℓ r : ℕ} (hℓ : ℓ.Prime) (hA : ℓ ∣ r ^ 2 + 3 * r + 3)
    (h : ℓ ∣ (r + 1) ^ 2 + 1) : False := by
  have h2 : r ^ 2 + 3 * r + 3 = ((r + 1) ^ 2 + 1) + (r + 1) := by ring
  rw [h2] at hA
  exact not_dvd_A_of_dvd_succ hℓ (h2 ▸ hA) ((Nat.dvd_add_right h).mp hA)

private theorem not_dvd_B_of_dvd_succ {ℓ r : ℕ} (hℓ : ℓ.Prime)
    (hB : ℓ ∣ r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1) (h : ℓ ∣ r + 1) : False := by
  have h1 : ℓ ∣ (r + 1) ^ 2 * (r ^ 2 + 2 * r) := Dvd.dvd.mul_right (dvd_pow h two_ne_zero) _
  have h2 : r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1 = (r + 1) ^ 2 * (r ^ 2 + 2 * r) + 1 := by
    ring
  rw [h2] at hB
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp hB))

private theorem not_dvd_B_of_dvd {ℓ r : ℕ} (hℓ : ℓ.Prime)
    (hB : ℓ ∣ r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1) (h : ℓ ∣ r) : False := by
  have h1 : ℓ ∣ r * (r ^ 3 + 4 * r ^ 2 + 5 * r + 2) := Dvd.dvd.mul_right h _
  have h2 : r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1 =
      r * (r ^ 3 + 4 * r ^ 2 + 5 * r + 2) + 1 := by ring
  rw [h2] at hB
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp hB))

private theorem not_dvd_B_of_dvd_sq {ℓ r : ℕ} (hℓ : ℓ.Prime)
    (h3 : ¬ 3 ∣ r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1)
    (hB : ℓ ∣ r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1) (h : ℓ ∣ (r + 1) ^ 2 + 1) : False := by
  have h1 : ℓ ∣ (r ^ 2 + 2 * r) * ((r + 1) ^ 2 + 1) := Dvd.dvd.mul_left h _
  have h2 : (r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1) + ((r + 1) ^ 2 + 1) =
      (r ^ 2 + 2 * r) * ((r + 1) ^ 2 + 1) + 3 := by ring
  have h4 : ℓ ∣ (r ^ 2 + 2 * r) * ((r + 1) ^ 2 + 1) + 3 := h2 ▸ Nat.dvd_add hB h
  have h5 : ℓ ∣ 3 := (Nat.dvd_add_right h1).mp h4
  have h6 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h5
  subst h6
  exact h3 hB

private theorem not_dvd_B_of_dvd_A {ℓ r : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hA : ℓ ∣ r ^ 2 + 3 * r + 3) (hB : ℓ ∣ r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1) :
    False := by
  have h2 : (r ^ 2 + 3 * r + 3) * (r ^ 2 + r + 1) =
      (r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1) + 2 * (r + 1) ^ 2 := by ring
  have h3 : ℓ ∣ (r ^ 2 + 3 * r + 3) * (r ^ 2 + r + 1) := Dvd.dvd.mul_right hA _
  rw [h2] at h3
  have h4 : ℓ ∣ 2 * (r + 1) ^ 2 := (Nat.dvd_add_right hB).mp h3
  rcases hℓ.dvd_mul.mp h4 with h5 | h5
  · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h5)
  · exact not_dvd_A_of_dvd_succ hℓ hA (hℓ.dvd_of_dvd_pow h5)

private theorem phi3_facts {ℓ r : ℕ} (hℓ : ℓ.Prime) (h3 : ¬ 3 ∣ r ^ 2 + 3 * r + 3)
    (hd : ℓ ∣ r ^ 2 + 3 * r + 3) :
    ℓ ∣ ((r + 1) ^ 3) ^ 2 * ((r + 1) ^ 3 - 1) * (((r + 1) ^ 3) ^ 2 + 1) ∧
      ¬ ℓ ∣ (r + 1) ^ 2 * (r + 1 - 1) * ((r + 1) ^ 2 + 1) := by
  have e1 : (r + 1) ^ 3 - 1 = r * (r ^ 2 + 3 * r + 3) := by
    have : (r + 1) ^ 3 = r * (r ^ 2 + 3 * r + 3) + 1 := by ring
    omega
  refine ⟨?_, fun h => ?_⟩
  · rw [e1]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Dvd.dvd.mul_left hd _) _) _
  · rw [Nat.add_sub_cancel] at h
    rcases hℓ.dvd_mul.mp h with h | h
    · rcases hℓ.dvd_mul.mp h with h | h
      · exact not_dvd_A_of_dvd_succ hℓ hd (hℓ.dvd_of_dvd_pow h)
      · exact not_dvd_A_of_dvd hℓ h3 hd h
    · exact not_dvd_A_of_dvd_sq hℓ hd h

private theorem phi12_facts {ℓ r : ℕ} (hℓ : ℓ.Prime)
    (h3 : ¬ 3 ∣ r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1)
    (hd : ℓ ∣ r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1) :
    ℓ ∣ ((r + 1) ^ 3) ^ 2 * ((r + 1) ^ 3 - 1) * (((r + 1) ^ 3) ^ 2 + 1) ∧
      ¬ ℓ ∣ (r + 1) ^ 2 * (r + 1 - 1) * ((r + 1) ^ 2 + 1) := by
  have e2 : ((r + 1) ^ 3) ^ 2 + 1 =
      ((r + 1) ^ 2 + 1) * (r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1) := by ring
  refine ⟨?_, fun h => ?_⟩
  · rw [e2]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hd _) _
  · rw [Nat.add_sub_cancel] at h
    rcases hℓ.dvd_mul.mp h with h | h
    · rcases hℓ.dvd_mul.mp h with h | h
      · exact not_dvd_B_of_dvd_succ hℓ hd (hℓ.dvd_of_dvd_pow h)
      · exact not_dvd_B_of_dvd hℓ hd h
    · exact not_dvd_B_of_dvd_sq hℓ h3 hd h

theorem exists_two_odd_primes_of_even (q₀ : ℕ) (h2 : 2 ≤ q₀) (hev : q₀ % 2 = 0) (h3 : q₀ % 3 = 2) :
    ∃ ℓ₁ ℓ₂ : ℕ, ℓ₁.Prime ∧ ℓ₂.Prime ∧ ℓ₁ ≠ ℓ₂ ∧ ℓ₁ ≠ 2 ∧ ℓ₂ ≠ 2 ∧
      ∀ ℓ : ℕ, (ℓ = ℓ₁ ∨ ℓ = ℓ₂) →
        ℓ ∣ (q₀ ^ 3) ^ 2 * (q₀ ^ 3 - 1) * ((q₀ ^ 3) ^ 2 + 1) ∧
        ¬ ℓ ∣ q₀ ^ 2 * (q₀ - 1) * (q₀ ^ 2 + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q₀ = r + 1 := ⟨q₀ - 1, by omega⟩
  have hr3 : r % 3 = 1 := by omega
  have hr2 : r % 2 = 1 := by omega
  have hr1 : 1 ≤ r := by omega
  have p2 : r ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hr2]
  have p3 : r ^ 3 % 2 = 1 := by rw [Nat.pow_mod, hr2]
  have p4 : r ^ 4 % 2 = 1 := by rw [Nat.pow_mod, hr2]
  have t2 : r ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hr3]
  have t3 : r ^ 3 % 3 = 1 := by rw [Nat.pow_mod, hr3]
  have t4 : r ^ 4 % 3 = 1 := by rw [Nat.pow_mod, hr3]
  have hA3 : ¬ 3 ∣ r ^ 2 + 3 * r + 3 := by omega
  have hB3 : ¬ 3 ∣ r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1 := by omega
  have hA1 : r ^ 2 + 3 * r + 3 ≠ 1 := by omega
  have hB1 : r ^ 4 + 4 * r ^ 3 + 5 * r ^ 2 + 2 * r + 1 ≠ 1 := by omega
  obtain ⟨ℓ₁, hℓ₁, hd₁⟩ := Nat.exists_prime_and_dvd hA1
  obtain ⟨ℓ₂, hℓ₂, hd₂⟩ := Nat.exists_prime_and_dvd hB1
  have hℓ₁2 : ℓ₁ ≠ 2 := by
    rintro rfl
    omega
  have hℓ₂2 : ℓ₂ ≠ 2 := by
    rintro rfl
    omega
  refine ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, ?_, hℓ₁2, hℓ₂2, ?_⟩
  · rintro rfl
    exact not_dvd_B_of_dvd_A hℓ₁ hℓ₁2 hd₁ hd₂
  · rintro ℓ (rfl | rfl)
    · exact phi3_facts hℓ₁ hA3 hd₁
    · exact phi12_facts hℓ₂ hB3 hd₂

theorem exists_two_odd_primes (b : ℕ) :
    ∃ ℓ₁ ℓ₂ : ℕ, ℓ₁.Prime ∧ ℓ₂.Prime ∧ ℓ₁ ≠ ℓ₂ ∧ ℓ₁ ≠ 2 ∧ ℓ₂ ≠ 2 ∧
      ∀ ℓ : ℕ, (ℓ = ℓ₁ ∨ ℓ = ℓ₂) →
        ℓ ∣ ((2 ^ (2 * b + 1)) ^ 3) ^ 2 * ((2 ^ (2 * b + 1)) ^ 3 - 1) *
          (((2 ^ (2 * b + 1)) ^ 3) ^ 2 + 1) ∧
        ¬ ℓ ∣ (2 ^ (2 * b + 1)) ^ 2 * (2 ^ (2 * b + 1) - 1) * ((2 ^ (2 * b + 1)) ^ 2 + 1) := by
  refine exists_two_odd_primes_of_even (2 ^ (2 * b + 1)) ?_ ?_ ?_
  · exact Nat.le_self_pow (by omega) 2
  · rw [pow_succ]
    omega
  · rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

end CFSG.LocalAnalysis.UniquenessCase.UCK.SzArith
