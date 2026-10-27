module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.H13.P31NT

theorem two_pow_add_one_ne_pow_three {k a : ℕ} (hk : 3 < k) : 2 ^ k + 1 ≠ 3 ^ a := by
  intro h
  have h2 : ∀ t : ℕ, 2 ^ (t + 4) % 80 = 16 ∨ 2 ^ (t + 4) % 80 = 32 ∨
      2 ^ (t + 4) % 80 = 64 ∨ 2 ^ (t + 4) % 80 = 48 := by
    intro t
    induction t with
    | zero => norm_num
    | succ n ih =>
      rw [show n + 1 + 4 = (n + 4) + 1 by omega, pow_succ, Nat.mul_mod]
      rcases ih with h' | h' | h' | h' <;> rw [h'] <;> norm_num
  have h3 : ∀ b : ℕ, 3 ^ b % 80 = 1 ∨ 3 ^ b % 80 = 3 ∨ 3 ^ b % 80 = 9 ∨ 3 ^ b % 80 = 27 := by
    intro b
    induction b with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h' | h' | h' | h' <;> rw [h'] <;> norm_num
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 4 := ⟨k - 4, by omega⟩
  have e1 := h2 t
  have e2 := h3 a
  omega

theorem exists_prime_ge_five_dvd_two_pow_add_one {k : ℕ} (hk : 2 ≤ k) (hk3 : k ≠ 3) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ 2 ^ k + 1 := by
  rcases (show k = 2 ∨ 4 ≤ k by omega) with rfl | hk4
  · exact ⟨5, by norm_num, le_refl 5, by norm_num⟩
  · by_contra hcon
    have hne : 2 ^ k + 1 ≠ 0 := by positivity
    have hfac : 2 ^ k + 1 = 3 ^ (2 ^ k + 1).primeFactorsList.length := by
      apply Nat.eq_prime_pow_of_unique_prime_dvd hne
      intro d hd hdvd
      by_contra hd3
      have hd2 : d ≠ 2 := by
        rintro rfl
        have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
        omega
      have hd5 : 5 ≤ d := by
        have h2 := hd.two_le
        by_contra h5
        have h5' : d < 5 := by omega
        interval_cases d
        · exact hd2 rfl
        · exact hd3 rfl
        · norm_num at hd
      exact hcon ⟨d, hd, hd5, hdvd⟩
    exact two_pow_add_one_ne_pow_three (by omega) hfac

theorem padicValNat_three_two_pow_sub_one {m : ℕ} (hm : Even m) (hm0 : 0 < m) :
    padicValNat 3 (2 ^ m - 1) = 1 + padicValNat 3 m := by
  obtain ⟨j, rfl⟩ := hm
  have hj : j ≠ 0 := by omega
  have h4 : (2 : ℕ) ^ (j + j) = 4 ^ j := by
    rw [← two_mul, pow_mul, show ((2 : ℕ) ^ 2) = 4 by norm_num]
  have hmul : padicValNat 3 (2 * j) = padicValNat 3 2 + padicValNat 3 j :=
    padicValNat.mul (by norm_num) (by omega)
  have h32 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have hv2 : padicValNat 3 (j + j) = padicValNat 3 j := by
    rw [show j + j = 2 * j by omega, hmul, h32, zero_add]
  have key := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) (n := j) ⟨1, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) hj
  rw [one_pow, show (4 : ℕ) - 1 = 3 by norm_num, padicValNat_self] at key
  rw [hv2, h4]
  exact key

theorem not_two_pow_odd_modEq_one {p k j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ 2 ^ k + 1)
    (hj : Odd j) : ¬ 2 ^ j ≡ 1 [MOD p] := by
  intro h
  have hk0 : ((2 ^ k + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpk
  have hk : (2 : ZMod p) ^ k = -1 := by
    push_cast at hk0
    linear_combination hk0
  have hj1 : (2 : ZMod p) ^ j = 1 := by
    have h' := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    push_cast at h'
    exact h'
  have hdj : orderOf (2 : ZMod p) ∣ j := orderOf_dvd_of_pow_eq_one hj1
  have hd2k : orderOf (2 : ZMod p) ∣ 2 * k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul', hk]
    norm_num
  have hdk : ¬ orderOf (2 : ZMod p) ∣ k := by
    intro hdk
    have h1 : (2 : ZMod p) ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp hdk
    have h2 : (2 : ZMod p) = 0 := by linear_combination hk - h1
    have h3 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    have h4 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
  have hcop : Nat.Coprime (orderOf (2 : ZMod p)) 2 :=
    Nat.coprime_two_right.mpr (hj.of_dvd_nat hdj)
  exact hdk (Nat.Coprime.dvd_of_dvd_mul_left hcop hd2k)

theorem three_dvd_two_pow_sub_one_iff {m : ℕ} : 3 ∣ 2 ^ m - 1 ↔ Even m := by
  have h1 : ∀ t : ℕ, 2 ^ (2 * t) % 3 = 1 := by
    intro t
    rw [pow_mul, Nat.pow_mod]
    norm_num
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' m
  · constructor
    · intro _
      exact even_two_mul t
    · intro _
      have := h1 t
      omega
  · have hY := h1 t
    rw [pow_succ]
    constructor
    · intro h
      exfalso
      omega
    · rintro ⟨r, hr⟩
      omega

end CFSG.Quasithin.H13.P31NT
