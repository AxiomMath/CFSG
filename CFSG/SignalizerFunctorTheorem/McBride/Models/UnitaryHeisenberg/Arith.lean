module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg

theorem two_pow_mod_nine {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    2 ^ p % 9 = 2 ∨ 2 ^ p % 9 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  have h6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  have key : 2 ^ p % 9 = 2 ^ (p % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod p 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  rcases h6 with h | h <;> rw [key, h] <;> norm_num

theorem exists_card_psu3 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∃ T : ℕ, Nat.card (PSU3 2 p) = 9 * T ∧ ¬ 3 ∣ T := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  rw [NearSolvable.card_psu3_of_odd hodd]
  set q := 2 ^ p with hq
  have hq9 := two_pow_mod_nine hp h5
  rw [← hq] at hq9
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hq27 : q % 27 = 2 ∨ q % 27 = 11 ∨ q % 27 = 20 ∨ q % 27 = 5 ∨ q % 27 = 14 ∨
      q % 27 = 23 := by omega
  have hA : (q ^ 3 + 1) % 27 = 9 ∨ (q ^ 3 + 1) % 27 = 18 := by
    rcases hq27 with h | h | h | h | h | h <;> simp [Nat.add_mod, Nat.pow_mod, h]
  have hq2 : q ^ 2 % 9 = 4 ∨ q ^ 2 % 9 = 7 := by
    rcases hq9 with h | h <;> simp [Nat.pow_mod, h]
  have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  obtain ⟨A, hA'⟩ : ∃ A, q ^ 3 + 1 = 9 * A := ⟨(q ^ 3 + 1) / 9, by omega⟩
  obtain ⟨B, hB'⟩ : ∃ B, q ^ 2 - 1 = 3 * B := ⟨(q ^ 2 - 1) / 3, by omega⟩
  have hA3 : ¬ 3 ∣ A := fun ⟨A', hA''⟩ => by omega
  have hB3 : ¬ 3 ∣ B := fun ⟨B', hB''⟩ => by omega
  have hq3 : ¬ 3 ∣ q := fun h => by omega
  refine ⟨q ^ 3 * A * B, ?_, ?_⟩
  · have : q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) = 3 * (9 * (q ^ 3 * A * B)) := by
      rw [hA', hB']; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  · intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · exact hq3 (Nat.prime_three.dvd_of_dvd_pow h)
      · exact hA3 h
    · exact hB3 h

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg
