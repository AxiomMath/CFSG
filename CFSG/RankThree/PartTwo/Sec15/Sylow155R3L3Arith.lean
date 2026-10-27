module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

theorem even_exponent_of_two_pow_mod_three_one {f : ℕ} (h : 2 ^ f % 3 = 1) : Even f := by
  rcases Nat.even_or_odd f with hf | ⟨m, hm⟩
  · exact hf
  · exfalso
    have h4 : 4 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have h2 : 2 ^ f = 4 ^ m * 2 := by
      rw [hm, pow_succ, pow_mul]
      norm_num
    omega

private theorem three_dvd_of_two_pow_mod_seven {f : ℕ} (h : 2 ^ f % 7 = 1) : 3 ∣ f := by
  have key : 2 ^ f = 8 ^ (f / 3) * 2 ^ (f % 3) := by
    conv_lhs => rw [← Nat.div_add_mod f 3]
    rw [pow_add, pow_mul]
    norm_num
  have h8 : 8 ^ (f / 3) % 7 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [key, Nat.mul_mod, h8, one_mul, Nat.mod_mod] at h
  rcases (by omega : f % 3 = 0 ∨ f % 3 = 1 ∨ f % 3 = 2) with h0 | h1 | h2
  · omega
  · rw [h1] at h
    norm_num at h
  · rw [h2] at h
    norm_num at h

private theorem two_pow_mod_nine_of_dvd_six {f : ℕ} (h : 6 ∣ f) : 2 ^ f % 9 = 1 := by
  obtain ⟨s, rfl⟩ := h
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem exists_dvd_or_prime_of_two_pow_sub_one {f : ℕ} (hf : Even f) (hf2 : 2 ≤ f) :
    9 ∣ 2 ^ f - 1 ∨ 5 ∣ 2 ^ f - 1 ∨ f = 2 ∨ ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ p ∣ 2 ^ f - 1 := by
  by_contra hcon
  simp only [not_or, not_exists, not_and] at hcon
  obtain ⟨h9, h5, hf2', hp⟩ := hcon
  have hf2mod : f % 2 = 0 := Nat.even_iff.mp hf
  have h2f3 : 2 ^ f % 3 = 1 := by
    obtain ⟨m, hm⟩ := hf
    rw [hm, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
  have h2dvd : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ f - 1 = N := ⟨_, rfl⟩
  rw [hN] at h9 h5 hp
  have hprime : ∀ p : ℕ, p.Prime → p ∣ N → p = 3 ∨ p = 7 := by
    intro p hpp hpd
    have hp2 : 2 ≤ p := hpp.two_le
    have hp11 : p < 11 := by
      by_contra h11
      exact hp p hpp (by omega) hpd
    interval_cases p <;> first | omega | simp
  obtain ⟨M, hM⟩ : 3 ∣ N := by omega
  have h3M : ¬ 3 ∣ M := by omega
  by_cases h7 : 7 ∣ N
  ·
    have h2f7 : 2 ^ f % 7 = 1 := by omega
    have h3f : 3 ∣ f := three_dvd_of_two_pow_mod_seven h2f7
    have h2f9 : 2 ^ f % 9 = 1 := two_pow_mod_nine_of_dvd_six (by omega)
    omega
  ·
    have hM1 : M = 1 := by
      by_contra hM1
      have hmp : (Nat.minFac M).Prime := Nat.minFac_prime hM1
      have hmd : Nat.minFac M ∣ N := by
        rw [hM]
        exact Dvd.dvd.mul_left (Nat.minFac_dvd M) 3
      rcases hprime _ hmp hmd with h | h
      · have h3 : 3 ∣ M := by
          rw [← h]
          exact Nat.minFac_dvd M
        exact h3M h3
      · have h7' : 7 ∣ N := by
          rw [← h]
          exact hmd
        exact h7 h7'
    have h4 : 2 ^ f = 4 := by omega
    have h22 : (2 : ℕ) ^ f = 2 ^ 2 := by norm_num [h4]
    exact hf2' (Nat.pow_right_injective (le_refl 2) h22)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
