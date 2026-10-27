module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

private theorem modEq_of_cube_modEq_of_period {p k : ℕ} (hk : 0 < k)
    (h2 : (2 : ZMod p) ^ k = 1) (hm : (-1 : ZMod p) ^ k = 1)
    (hsmall : ∀ r : Fin k, (2 : ZMod p) ^ (3 * r.val) = -(-1 : ZMod p) ^ r.val →
      (2 : ZMod p) ^ r.val = -(-1 : ZMod p) ^ r.val)
    {n : ℕ} (hdiv : (2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) :
    (2 : ℤ) ^ n ≡ -R891Pi n [ZMOD p] := by
  have hdivZ : (2 : ZMod p) ^ (3 * n) = -(-1 : ZMod p) ^ n := by
    simpa only [R891Pi, Int.cast_neg, Int.cast_pow, Int.cast_ofNat, Int.cast_one]
      using (ZMod.intCast_eq_intCast_iff _ _ p).mpr hdiv
  have ht := pow_eq_pow_mod n h2
  have hm' := pow_eq_pow_mod n hm
  rw [Nat.mul_comm 3 n, pow_mul, ht, hm'] at hdivZ
  have hres : (2 : ZMod p) ^ (3 * (n % k)) = -(-1 : ZMod p) ^ (n % k) := by
    simpa only [Nat.mul_comm 3 (n % k), pow_mul] using hdivZ
  have h := hsmall ⟨n % k, Nat.mod_lt n hk⟩ hres
  have hZ : (2 : ZMod p) ^ n = -(-1 : ZMod p) ^ n := by
    rwa [ht, hm']
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  simpa only [R891Pi, Int.cast_neg, Int.cast_pow, Int.cast_ofNat, Int.cast_one] using hZ

private theorem ne_two_of_R891_congruences {n : ℕ}
    (hdiv : (2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD 2])
    (hndiv : ¬ (2 : ℤ) ^ n ≡ -R891Pi n [ZMOD 2]) : False := by
  by_cases hn : n = 0
  · subst hn
    norm_num [R891Pi, Int.ModEq] at hndiv
  · have hdivZ : (2 : ZMod 2) ^ (3 * n) = -(-1 : ZMod 2) ^ n := by
      simpa only [R891Pi, Int.cast_neg, Int.cast_pow, Int.cast_ofNat, Int.cast_one]
        using (ZMod.intCast_eq_intCast_iff _ _ 2).mpr hdiv
    have he : 3 * n ≠ 0 := by omega
    rw [show (2 : ZMod 2) = 0 by decide, zero_pow he,
      show (-1 : ZMod 2) = 1 by decide, one_pow,
      show (-1 : ZMod 2) = 1 by decide] at hdivZ
    exact zero_ne_one hdivZ

theorem prime_exclusions_of_R891_congruences (n p : ℕ) (_hp : p.Prime)
    (hdiv : (2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p])
    (hndiv : ¬ (2 : ℤ) ^ n ≡ -R891Pi n [ZMOD p]) :
    p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 11 ∧ p ≠ 19 ∧ p ≠ 31 := by
  constructor
  · rintro rfl
    exact ne_two_of_R891_congruences hdiv hndiv
  constructor
  · rintro rfl
    exact hndiv (modEq_of_cube_modEq_of_period (k := 2) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hdiv)
  constructor
  · rintro rfl
    exact hndiv (modEq_of_cube_modEq_of_period (k := 4) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hdiv)
  constructor
  · rintro rfl
    exact hndiv (modEq_of_cube_modEq_of_period (k := 10) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hdiv)
  constructor
  · rintro rfl
    exact hndiv (modEq_of_cube_modEq_of_period (k := 18) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hdiv)
  · rintro rfl
    exact hndiv (modEq_of_cube_modEq_of_period (k := 10) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hdiv)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
