module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

namespace SL3G

section Arith

private lemma odd_three : Odd 3 := ⟨1, rfl⟩

private lemma three_dvd_sub_one_of_mod_eq_one {a : ℕ} (ha : a % 3 = 1) : 3 ∣ a - 1 := by
  have h1 : 1 ≤ a := by omega
  have h : a ≡ 1 [MOD 3] := by
    rw [Nat.ModEq]
    rw [ha]
  exact (Nat.modEq_iff_dvd' h1).mp h.symm

private lemma not_three_dvd_of_mod_eq_one {a : ℕ} (ha : a % 3 = 1) : ¬ 3 ∣ a := by
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

private lemma not_three_dvd_of_mod_eq_two {a : ℕ} (ha : a % 3 = 2) : ¬ 3 ∣ a := by
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

private lemma three_dvd_add_one_of_mod_eq_two {a : ℕ} (ha : a % 3 = 2) : 3 ∣ a + 1 := by
  have : (a + 1) % 3 = 0 := by
    rw [Nat.add_mod, ha]
  exact Nat.dvd_of_mod_eq_zero this

private lemma pow_mod_three_of_mod_eq_one {a m : ℕ} (ha : a % 3 = 1) : a ^ m % 3 = 1 := by
  rw [Nat.pow_mod, ha, one_pow]
  norm_num

private lemma pow_mod_three_of_mod_eq_two_odd {a m : ℕ} (ha : a % 3 = 2) (hm : Odd m) :
    a ^ m % 3 = 2 := by
  rw [Nat.pow_mod, ha]
  obtain ⟨n, rfl⟩ := hm
  rw [pow_succ, pow_mul]
  have h4 : ((2 : ℕ) ^ 2) ^ n % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [Nat.mul_mod, h4]

private lemma pow_mod_three_of_mod_eq_two_even {a m : ℕ} (ha : a % 3 = 2) (hm : Even m) :
    a ^ m % 3 = 1 := by
  rw [Nat.pow_mod, ha]
  obtain ⟨n, rfl⟩ := hm
  rw [← two_mul, pow_mul]
  rw [Nat.pow_mod]
  norm_num

private lemma sub_one_mod_three_of_mod_eq_two {a : ℕ} (ha : a % 3 = 2) : (a - 1) % 3 = 1 := by
  have hdecomp : a = 3 * (a / 3) + 2 := by
    have := Nat.div_add_mod a 3
    omega
  have hsub : a - 1 = 1 + 3 * (a / 3) := by omega
  rw [hsub, Nat.add_mul_mod_self_left]

private lemma not_three_dvd_sub_one_of_mod_eq_two {a : ℕ} (ha : a % 3 = 2) : ¬ 3 ∣ a - 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, sub_one_mod_three_of_mod_eq_two ha]
  norm_num

private lemma unitary_valuation {r k : ℕ} (hr : r % 3 = 2)
    (hk1 : 3 ^ k ∣ r ^ 3 + 1) (hk2 : ¬ 3 ^ (k + 1) ∣ r ^ 3 + 1) :
    padicValNat 3 (r + 1) = k - 1 ∧ 1 ≤ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : r ^ 3 + 1 ≠ 0 := by positivity
  have hvN_le : k ≤ padicValNat 3 (r ^ 3 + 1) := (padicValNat_dvd_iff_le hN).mp hk1
  have hvN_lt : padicValNat 3 (r ^ 3 + 1) < k + 1 := by
    by_contra h
    exact hk2 ((padicValNat_dvd_iff_le hN).mpr (by omega))
  have hvN : padicValNat 3 (r ^ 3 + 1) = k := le_antisymm (by omega) hvN_le
  have h3r : ¬ 3 ∣ r := not_three_dvd_of_mod_eq_two hr
  have h3rp1 : 3 ∣ r + 1 := three_dvd_add_one_of_mod_eq_two hr
  have hvs : padicValNat 3 (r ^ 3 + 1) = padicValNat 3 (r + 1) + 1 := by
    have h := padicValNat.pow_add_pow (p := 3) (x := r) (y := 1)
      odd_three h3rp1 h3r odd_three
    simpa [padicValNat_self] using h
  have hv_rp1 : padicValNat 3 (r + 1) = k - 1 := by omega
  have hk1' : 1 ≤ k := by
    have : 1 ≤ padicValNat 3 (r + 1) :=
      (padicValNat_dvd_iff_le (by positivity : r + 1 ≠ 0)).mp (by simpa using h3rp1)
    omega
  exact ⟨hv_rp1, hk1'⟩

private lemma unitary_even {r k m : ℕ} (hr : r % 3 = 2) (hm : Even m) (hm3 : ¬ 3 ∣ m)
    (hv : padicValNat 3 (r + 1) = k - 1) (hk : 1 ≤ k) :
    ¬ 3 ^ k ∣ r ^ m - 1 ∧ ¬ 3 ^ k ∣ r ^ m + 1 ∧ ¬ 3 ^ k ∣ r ^ m := by
  have hr1 : 1 < r := by omega
  have hm0 : m ≠ 0 := by rintro rfl; exact hm3 (dvd_zero 3)
  have h3dvd : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have hpow : r ^ m % 3 = 1 := pow_mod_three_of_mod_eq_two_even hr hm
  obtain ⟨n, hn⟩ := hm
  have hn3 : ¬ 3 ∣ n := by
    intro h
    exact hm3 (hn ▸ dvd_add h h)
  have hn0 : n ≠ 0 := by
    intro h
    exact hm3 (hn ▸ by rw [h]; exact dvd_zero 3)
  have hm_pow : r ^ m = (r ^ 2) ^ n := by rw [hn, ← two_mul, pow_mul]
  have hr2m1 : 3 ∣ r ^ 2 - 1 := by
    have h : r ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hr]
    exact three_dvd_sub_one_of_mod_eq_one h
  have hr2nd : ¬ 3 ∣ r ^ 2 := by
    have h : r ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hr]
    exact not_three_dvd_of_mod_eq_one h
  have hn3v : padicValNat 3 n = 0 := padicValNat.eq_zero_of_not_dvd hn3
  have hvs_n : padicValNat 3 ((r ^ 2) ^ n - 1) = padicValNat 3 (r ^ 2 - 1) := by
    have h := padicValNat.pow_sub_pow (p := 3) (x := r ^ 2) (y := 1)
      odd_three (one_lt_pow₀ hr1 (by omega)) hr2m1 hr2nd hn0
    rw [one_pow, hn3v, add_zero] at h
    exact h
  have hsq : r ^ 2 - 1 = (r + 1) * (r - 1) := by simpa using Nat.pow_two_sub_pow_two r 1
  have hmul : padicValNat 3 ((r + 1) * (r - 1)) =
      padicValNat 3 (r + 1) + padicValNat 3 (r - 1) :=
    padicValNat.mul (by positivity) (Nat.sub_ne_zero_of_lt hr1)
  have hr1v : padicValNat 3 (r - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (not_three_dvd_sub_one_of_mod_eq_two hr)
  have hvm1 : padicValNat 3 (r ^ m - 1) = k - 1 := by
    rw [hm_pow, hvs_n, hsq, hmul, hr1v, add_zero, hv]
  have hrm1 : r ^ m - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_pow₀ hr1 hm0)
  have hnotm1 : ¬ 3 ^ k ∣ r ^ m - 1 := by
    rw [padicValNat_dvd_iff_le hrm1]
    omega
  have h3rm : ¬ 3 ∣ r ^ m := not_three_dvd_of_mod_eq_one hpow
  have h3rmp1 : ¬ 3 ∣ r ^ m + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hpow]
    norm_num
  exact ⟨hnotm1, fun h => h3rmp1 (h3dvd.trans h), fun h => h3rm (h3dvd.trans h)⟩

private lemma unitary_odd {r k m : ℕ} (hr : r % 3 = 2) (hm : Odd m) (hm3 : ¬ 3 ∣ m)
    (hv : padicValNat 3 (r + 1) = k - 1) (hk : 1 ≤ k) :
    ¬ 3 ^ k ∣ r ^ m - 1 ∧ ¬ 3 ^ k ∣ r ^ m + 1 ∧ ¬ 3 ^ k ∣ r ^ m := by
  have h3r : ¬ 3 ∣ r := not_three_dvd_of_mod_eq_two hr
  have h3rp1 : 3 ∣ r + 1 := three_dvd_add_one_of_mod_eq_two hr
  have hmv : padicValNat 3 m = 0 := padicValNat.eq_zero_of_not_dvd hm3
  have hvs_m : padicValNat 3 (r ^ m + 1) = k - 1 := by
    have h := padicValNat.pow_add_pow (p := 3) (x := r) (y := 1) odd_three h3rp1 h3r hm
    rw [one_pow, hv, hmv, add_zero] at h
    exact h
  have hrmp1 : r ^ m + 1 ≠ 0 := by positivity
  have hnotp1 : ¬ 3 ^ k ∣ r ^ m + 1 := by
    rw [padicValNat_dvd_iff_le hrmp1]
    omega
  have hpow : r ^ m % 3 = 2 := pow_mod_three_of_mod_eq_two_odd hr hm
  have h3rm : ¬ 3 ∣ r ^ m := not_three_dvd_of_mod_eq_two hpow
  have h3rm1 : ¬ 3 ∣ r ^ m - 1 := not_three_dvd_sub_one_of_mod_eq_two hpow
  have h3dvd : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  exact ⟨fun h => h3rm1 (h3dvd.trans h), hnotp1, fun h => h3rm (h3dvd.trans h)⟩

theorem arith_linear {r : ℕ} (hr1 : 1 < r) (hr : r % 3 = 1) {k : ℕ}
    (hk1 : 3 ^ k ∣ r ^ 3 - 1) (hk2 : ¬ 3 ^ (k + 1) ∣ r ^ 3 - 1) {m : ℕ} (hm : ¬ 3 ∣ m) :
    ¬ 3 ^ k ∣ r ^ m - 1 ∧ ¬ 3 ^ k ∣ r ^ m + 1 ∧ ¬ 3 ^ k ∣ r ^ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : r ^ 3 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_pow₀ hr1 (by omega))
  have hvN_le : k ≤ padicValNat 3 (r ^ 3 - 1) := (padicValNat_dvd_iff_le hN).mp hk1
  have hvN_lt : padicValNat 3 (r ^ 3 - 1) < k + 1 := by
    by_contra h
    exact hk2 ((padicValNat_dvd_iff_le hN).mpr (by omega))
  have hvN : padicValNat 3 (r ^ 3 - 1) = k := le_antisymm (by omega) hvN_le
  have h3r1 : 3 ∣ r - 1 := three_dvd_sub_one_of_mod_eq_one hr
  have h3r : ¬ 3 ∣ r := not_three_dvd_of_mod_eq_one hr
  have hvs : padicValNat 3 (r ^ 3 - 1) = padicValNat 3 (r - 1) + 1 := by
    have h := padicValNat.pow_sub_pow (p := 3) (x := r) (y := 1)
      odd_three hr1 h3r1 h3r (by omega : (3 : ℕ) ≠ 0)
    simpa [padicValNat_self] using h
  have hv_r1 : padicValNat 3 (r - 1) = k - 1 := by omega
  have hk1' : 1 ≤ k := by
    have : 1 ≤ padicValNat 3 (r - 1) :=
      (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hr1)).mp (by simpa using h3r1)
    omega
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  have hmv : padicValNat 3 m = 0 := padicValNat.eq_zero_of_not_dvd hm
  have hvs_m : padicValNat 3 (r ^ m - 1) = k - 1 := by
    have h := padicValNat.pow_sub_pow (p := 3) (x := r) (y := 1) odd_three hr1 h3r1 h3r hm0
    rw [one_pow, hv_r1, hmv, add_zero] at h
    exact h
  have hrm1 : r ^ m - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_pow₀ hr1 hm0)
  have hnot1 : ¬ 3 ^ k ∣ r ^ m - 1 := by
    rw [padicValNat_dvd_iff_le hrm1]
    omega
  have hpow : r ^ m % 3 = 1 := pow_mod_three_of_mod_eq_one hr
  have h3rm : ¬ 3 ∣ r ^ m := not_three_dvd_of_mod_eq_one hpow
  have h3rmp1 : ¬ 3 ∣ r ^ m + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hpow]
    norm_num
  have h3dvd : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  exact ⟨hnot1, fun h => h3rmp1 (h3dvd.trans h), fun h => h3rm (h3dvd.trans h)⟩

theorem arith_unitary {r : ℕ} (hr : r % 3 = 2) {k : ℕ}
    (hk1 : 3 ^ k ∣ r ^ 3 + 1) (hk2 : ¬ 3 ^ (k + 1) ∣ r ^ 3 + 1) {m : ℕ} (hm : ¬ 3 ∣ m) :
    ¬ 3 ^ k ∣ r ^ m - 1 ∧ ¬ 3 ^ k ∣ r ^ m + 1 ∧ ¬ 3 ^ k ∣ r ^ m := by
  obtain ⟨hv, hk⟩ := unitary_valuation hr hk1 hk2
  rcases Nat.even_or_odd m with hm_even | hm_odd
  · exact unitary_even hr hm_even hm hv hk
  · exact unitary_odd hr hm_odd hm hv hk

theorem exists_primitiveRoot_three {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) : ∃ ω : K, IsPrimitiveRoot ω 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hzp : IsPrimitiveRoot z 3 := by
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  exact ⟨(z : K), IsPrimitiveRoot.coe_units_iff.mpr hzp⟩

end Arith

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
