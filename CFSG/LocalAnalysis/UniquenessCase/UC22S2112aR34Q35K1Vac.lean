module

public import CFSG.Blueprint.Catalog
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)

theorem uc22s2112r34q35_ne_eleven_ne_thirteen {s m : ℕ} (hm : Odd m) (hsm : s ∣ 2 ^ m - 1) :
    s ≠ 11 ∧ s ≠ 13 := by
  obtain ⟨k, rfl⟩ := hm
  have hpow : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm]
  have hmod : 2 ^ (2 * k + 1) ≡ 1 [MOD s] :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hsm |>.symm
  constructor
  · rintro rfl
    have h1 : 2 ^ (2 * k + 1) % 11 = 1 := hmod
    rw [hpow] at h1
    have h45 : 4 ^ 5 ≡ 1 [MOD 11] := by decide
    have hk : 4 ^ k ≡ 4 ^ (k % 5) [MOD 11] := by
      conv_lhs => rw [← Nat.div_add_mod k 5]
      rw [pow_add, pow_mul]
      have h1 : (4 ^ 5) ^ (k / 5) ≡ 1 [MOD 11] := by
        simpa using h45.pow (k / 5)
      simpa using h1.mul (Nat.ModEq.refl (4 ^ (k % 5)))
    have h2 : 2 * 4 ^ k ≡ 2 * 4 ^ (k % 5) [MOD 11] :=
      (Nat.ModEq.refl 2).mul hk
    have h3 : (2 * 4 ^ (k % 5)) % 11 = 1 := by
      rw [← h1]
      exact h2.symm
    have hlt : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases h : k % 5 <;> norm_num [h] at h3
  · rintro rfl
    have h1 : 2 ^ (2 * k + 1) % 13 = 1 := hmod
    rw [hpow] at h1
    have h46 : 4 ^ 6 ≡ 1 [MOD 13] := by decide
    have hk : 4 ^ k ≡ 4 ^ (k % 6) [MOD 13] := by
      conv_lhs => rw [← Nat.div_add_mod k 6]
      rw [pow_add, pow_mul]
      have h1 : (4 ^ 6) ^ (k / 6) ≡ 1 [MOD 13] := by
        simpa using h46.pow (k / 6)
      simpa using h1.mul (Nat.ModEq.refl (4 ^ (k % 6)))
    have h2 : 2 * 4 ^ k ≡ 2 * 4 ^ (k % 6) [MOD 13] :=
      (Nat.ModEq.refl 2).mul hk
    have h3 : (2 * 4 ^ (k % 6)) % 13 = 1 := by
      rw [← h1]
      exact h2.symm
    have hlt : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases h : k % 6 <;> norm_num [h] at h3

theorem uc22s2112r34q35_alpha_psl4_three {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSL 4 3 1) (x : X) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) (hs13 : s ≠ 13) :
    orderOf x ≠ s := by
  intro hxs
  have hN : Nat.card X = 6065280 := by
    rw [hX.card_eq_lieOrd (by norm_num)]
    decide
  have hfac : 6065280 = 2 ^ 7 * (3 ^ 6 * (5 ^ 1 * 13 ^ 1)) := by norm_num
  have hdvd : s ∣ 6065280 := by
    rw [← hN]
    exact hxs ▸ orderOf_dvd_natCard x
  rw [hfac] at hdvd
  rcases (Nat.Prime.dvd_mul hs).mp hdvd with h2 | h
  · have := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_two h2
    omega
  rcases (Nat.Prime.dvd_mul hs).mp h with h3 | h
  · have := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_three h3
    omega
  rcases (Nat.Prime.dvd_mul hs).mp h with h5 | h13
  · have := Nat.prime_eq_prime_of_dvd_pow hs (by norm_num : Nat.Prime 5) h5
    omega
  · exact hs13 ((Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 13)).mp
      (by simpa using h13))

theorem uc22s2112r34q35_alpha_psl5_three {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSL 5 3 1) (x : X) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) (hs11 : s ≠ 11)
    (hs13 : s ≠ 13) : orderOf x ≠ s := by
  intro hxs
  have hN : Nat.card X = 237783237120 := by
    rw [hX.card_eq_lieOrd (by norm_num)]
    decide
  have hfac : 237783237120 = 2 ^ 9 * (3 ^ 10 * (5 ^ 1 * (11 ^ 2 * 13 ^ 1))) := by norm_num
  have hdvd : s ∣ 237783237120 := by
    rw [← hN]
    exact hxs ▸ orderOf_dvd_natCard x
  rw [hfac] at hdvd
  rcases (Nat.Prime.dvd_mul hs).mp hdvd with h2 | h
  · have := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_two h2
    omega
  rcases (Nat.Prime.dvd_mul hs).mp h with h3 | h
  · have := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_three h3
    omega
  rcases (Nat.Prime.dvd_mul hs).mp h with h5 | h
  · have := Nat.prime_eq_prime_of_dvd_pow hs (by norm_num : Nat.Prime 5) h5
    omega
  rcases (Nat.Prime.dvd_mul hs).mp h with h11 | h13
  · have := Nat.prime_eq_prime_of_dvd_pow hs (by norm_num : Nat.Prime 11) h11
    exact absurd this hs11
  · exact hs13 ((Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 13)).mp
      (by simpa using h13))

theorem uc22s2112r34q35_alpha_psp4_three {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSp 2 3 1) (x : X) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    orderOf x ≠ s := by
  intro hxs
  have hN : Nat.card X = 25920 := by
    rw [hX.card_eq_lieOrd (by norm_num)]
    decide
  have hfac : 25920 = 2 ^ 6 * (3 ^ 4 * 5 ^ 1) := by norm_num
  have hdvd : s ∣ 25920 := by
    rw [← hN]
    exact hxs ▸ orderOf_dvd_natCard x
  rw [hfac] at hdvd
  rcases (Nat.Prime.dvd_mul hs).mp hdvd with h2 | h
  · have := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_two h2
    omega
  rcases (Nat.Prime.dvd_mul hs).mp h with h3 | h5
  · have := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_three h3
    omega
  · have := Nat.prime_eq_prime_of_dvd_pow hs (by norm_num : Nat.Prime 5) h5
    omega

theorem uc22s2112r34q35_alpha_psp4_five {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSp 2 5 1) (x : X) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) (hs13 : s ≠ 13) :
    orderOf x ≠ s := by
  intro hxs
  have hN : Nat.card X = 4680000 := by
    rw [hX.card_eq_lieOrd (by norm_num)]
    decide
  have hfac : 4680000 = 2 ^ 6 * (3 ^ 2 * (5 ^ 4 * 13 ^ 1)) := by norm_num
  have hdvd : s ∣ 4680000 := by
    rw [← hN]
    exact hxs ▸ orderOf_dvd_natCard x
  rw [hfac] at hdvd
  rcases (Nat.Prime.dvd_mul hs).mp hdvd with h2 | h
  · have := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_two h2
    omega
  rcases (Nat.Prime.dvd_mul hs).mp h with h3 | h
  · have := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_three h3
    omega
  rcases (Nat.Prime.dvd_mul hs).mp h with h5 | h13
  · have := Nat.prime_eq_prime_of_dvd_pow hs (by norm_num : Nat.Prime 5) h5
    omega
  · exact hs13 ((Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 13)).mp
      (by simpa using h13))

end CFSG.LocalAnalysis.UniquenessCase.UC22
