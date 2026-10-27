module

public import CFSG.Open.Defs

import CFSG.GroupTheory.TwoPowOrderFactorization

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open

private lemma factorization_three_two : (2 : ℕ).factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (by norm_num)

private lemma factorization_three_three : (3 : ℕ).factorization 3 = 1 :=
  Nat.Prime.factorization_self Nat.prime_three

private lemma factorization_three_six : (6 : ℕ).factorization 3 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, factorization_three_two, factorization_three_three]

private lemma factorization_three_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization 3 = a.factorization 3 + b.factorization 3 := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

private lemma factorization_three_pow_of_not_dvd {q k : ℕ} (h3 : ¬ 3 ∣ q) :
    (q ^ k).factorization 3 = 0 := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    Nat.factorization_eq_zero_of_not_dvd h3, mul_zero]

private lemma factorization_three_gcd_eq_zero {m q : ℕ} (hm : ¬ 3 ∣ m) :
    (Nat.gcd m q).factorization 3 = 0 := by
  refine Nat.factorization_eq_zero_of_not_dvd ?_
  intro h
  exact hm (Nat.dvd_gcd_iff.mp h).1

private lemma pred_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  refine ⟨q + 1, ?_⟩
  change q ^ 2 - 1 ^ 2 = (q - 1) * (q + 1)
  rw [Nat.sq_sub_sq]
  ring

private lemma succ_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  refine ⟨q - 1, ?_⟩
  change q ^ 2 - 1 ^ 2 = (q + 1) * (q - 1)
  rw [Nat.sq_sub_sq]

private lemma three_dvd_sq_sub_one {q : ℕ} (h3 : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
    have h := Nat.mod_lt q (by norm_num : 0 < 3)
    have h0 : q % 3 ≠ 0 := fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
    omega
  have h1 : q ^ 2 % 3 = 1 := by
    rcases hq3 with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
  exact Nat.dvd_of_mod_eq_zero (by omega)

private lemma factorization_three_pow_add_one_eq_zero_of_mod_three_eq_one {q k : ℕ}
    (hq : q % 3 = 1) : (q ^ k + 1).factorization 3 = 0 := by
  have hmod : q ≡ 1 [MOD 3] := by
    show q % 3 = 1 % 3
    rw [hq]
  exact CFSG.GroupTheory.factorization_pow_add_one_eq_zero (q := q) (r := 3) (k := k)
    Nat.prime_three (by norm_num) hmod

private lemma factorization_three_pow_add_one_eq_zero_of_even {q k : ℕ} (h3 : ¬ 3 ∣ q)
    (hk : Even k) : (q ^ k + 1).factorization 3 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + m := hk
  have hmod : q ^ 2 ≡ 1 [MOD 3] := by
    show q ^ 2 % 3 = 1 % 3
    have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
      have h := Nat.mod_lt q (by norm_num : 0 < 3)
      have h0 : q % 3 ≠ 0 := fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
      omega
    rcases hq3 with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  have h := CFSG.GroupTheory.factorization_pow_add_one_eq_zero (q := q ^ 2) (r := 3) (k := m)
    Nat.prime_three (by norm_num) hmod
  have hmul : m + m = 2 * m := by omega
  rw [hmul, pow_mul]
  exact h

private lemma factorization_three_pow_sub_one_eq_zero_of_odd {q k : ℕ} (hq : q % 3 = 2)
    (hk : Odd k) : (q ^ k - 1).factorization 3 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := hk
  refine Nat.factorization_eq_zero_of_not_dvd ?_
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have hm : (q ^ 2) ^ m % 3 = 1 := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [pow_succ, Nat.mul_mod, ih, hq2]
  have hpow : q ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, hm, Nat.mul_mod, hq]
  have hpos : 1 ≤ q ^ (2 * m + 1) := Nat.one_le_pow _ _ (by omega)
  omega

private lemma factorization_three_pow_sub_one_of_mod_three_eq_one {q k : ℕ} (hq : q % 3 = 1)
    (h2 : 2 ≤ q) (hk : k ≠ 0) :
    (q ^ k - 1).factorization 3 = (q - 1).factorization 3 + k.factorization 3 := by
  have h3 : ¬ 3 ∣ q := by omega
  have hd : 3 ∣ q - 1 := by omega
  have hlt : 1 < q := by omega
  have h := padicValNat.pow_sub_pow (p := 3) (x := q) (y := 1) (by decide) hlt
    (by simpa using hd) h3 (n := k) hk
  rw [one_pow] at h
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    Nat.factorization_def _ Nat.prime_three]
  exact h

private lemma factorization_three_pow_add_one_of_mod_three_eq_two {q k : ℕ} (hq : q % 3 = 2)
    (hk : Odd k) :
    (q ^ k + 1).factorization 3 = (q + 1).factorization 3 + k.factorization 3 := by
  have h3 : ¬ 3 ∣ q := by omega
  have hd : 3 ∣ q + 1 := by omega
  have h := padicValNat.pow_add_pow (p := 3) (x := q) (y := 1) (by decide) (by simpa using hd)
    h3 (n := k) hk
  rw [one_pow] at h
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    Nat.factorization_def _ Nat.prime_three]
  exact h

private lemma factorization_three_pow_two_mul_sub_one {q m : ℕ} (h3 : ¬ 3 ∣ q) (h2 : 2 ≤ q)
    (hm : m ≠ 0) :
    (q ^ (2 * m) - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + m.factorization 3 := by
  have hq2gt : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have hd : 3 ∣ q ^ 2 - 1 := three_dvd_sq_sub_one h3
  have h3q2 : ¬ 3 ∣ q ^ 2 := fun h => h3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  have h := padicValNat.pow_sub_pow (p := 3) (x := q ^ 2) (y := 1) (by decide) hq2gt
    (by simpa using hd) h3q2 (n := m) hm
  rw [one_pow, ← pow_mul] at h
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    Nat.factorization_def _ Nat.prime_three]
  exact h

private lemma factorization_three_pow_eight_add_pow_four_add_one {q : ℕ} (h3 : ¬ 3 ∣ q)
    (h2 : 2 ≤ q) : (q ^ 8 + q ^ 4 + 1).factorization 3 = 1 := by
  have hgeom : (q ^ 4 - 1) * (q ^ 8 + q ^ 4 + 1) = q ^ 12 - 1 := by
    have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow 4 q (by omega)
    have h := geom_sum_mul_add (x := q ^ 4 - 1) 3
    rw [Nat.sub_add_cancel h4] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero] at h
    norm_num at h
    have e2 : (q ^ 4) ^ 2 = q ^ 8 := by rw [← pow_mul]
    have e3 : (q ^ 4) ^ 3 = q ^ 12 := by rw [← pow_mul]
    rw [e2, e3] at h
    have h' : (q ^ 8 + q ^ 4 + 1) * (q ^ 4 - 1) + 1 = q ^ 12 := by
      rw [← h]
      ring
    have h'' : (q ^ 8 + q ^ 4 + 1) * (q ^ 4 - 1) = q ^ 12 - 1 := by omega
    rwa [mul_comm] at h''
  have hpos : 0 < q ^ 4 - 1 := by
    have h16 : (2 : ℕ) ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left h2 4
    omega
  have hdvd : q ^ 4 - 1 ∣ q ^ 12 - 1 := ⟨q ^ 8 + q ^ 4 + 1, hgeom.symm⟩
  have hqdiv : q ^ 8 + q ^ 4 + 1 = (q ^ 12 - 1) / (q ^ 4 - 1) := by
    rw [← hgeom, Nat.mul_div_cancel_left _ hpos]
  have h12 : (q ^ 12 - 1).factorization 3 =
      (q ^ 2 - 1).factorization 3 + (6 : ℕ).factorization 3 := by
    simpa using factorization_three_pow_two_mul_sub_one (q := q) (m := 6) h3 h2 (by norm_num)
  have h4f : (q ^ 4 - 1).factorization 3 =
      (q ^ 2 - 1).factorization 3 + (2 : ℕ).factorization 3 := by
    simpa using factorization_three_pow_two_mul_sub_one (q := q) (m := 2) h3 h2 (by norm_num)
  rw [hqdiv, Nat.factorization_div hdvd]
  change (q ^ 12 - 1).factorization 3 - (q ^ 4 - 1).factorization 3 = 1
  rw [h12, h4f, factorization_three_six, factorization_three_two]
  omega

private lemma ordA_two_eq (q : ℕ) :
    ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  rw [ordA, show 2 * (2 + 1) / 2 = 3 by norm_num,
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 1 + 1)]
  simp

private lemma ordA_three_eq (q : ℕ) :
    ordA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q - 1) := by
  rw [ordA, show 3 * (3 + 1) / 2 = 6 by norm_num,
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 1 + 1)]
  simp

private lemma ordA_four_eq (q : ℕ) :
    ordA 4 q = q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)) /
      Nat.gcd 5 (q - 1) := by
  rw [ordA, show 4 * (4 + 1) / 2 = 10 by norm_num,
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 1 + 1)]
  simp

private lemma ordTwistedA_two_eq (q : ℕ) :
    ordTwistedA 2 q = q ^ 3 * ((((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) *
      (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat)) / Nat.gcd 3 (q + 1) := by
  rw [ordTwistedA, show 2 * (2 + 1) / 2 = 3 by norm_num,
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 1 + 1)]
  simp

private lemma ordTwistedA_three_eq (q : ℕ) :
    ordTwistedA 3 q = q ^ 6 * ((((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) *
      (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) * (((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat)) /
      Nat.gcd 4 (q + 1) := by
  rw [ordTwistedA, show 3 * (3 + 1) / 2 = 6 by norm_num,
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 1 + 1)]
  simp

private lemma ordTwistedA_four_eq (q : ℕ) :
    ordTwistedA 4 q = q ^ 10 * ((((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) *
      (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) * (((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat) *
      (((q : ℤ) ^ 5 - (-1 : ℤ) ^ 5).toNat)) / Nat.gcd 5 (q + 1) := by
  rw [ordTwistedA, show 4 * (4 + 1) / 2 = 10 by norm_num,
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 1 + 1)]
  simp

private lemma ordBC_two_eq (q : ℕ) :
    ordBC 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) / Nat.gcd 2 (q - 1) := by
  rw [ordBC, show 2 * 2 = 4 by norm_num,
    Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 2),
    Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 1)]
  simp

private lemma toNat_sq_sub_one (q : ℕ) (hq : 1 ≤ q) :
    (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := by
  have h1 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow 2 q (by omega))]
    push_cast
    ring
  rw [h1, Int.toNat_natCast]

private lemma toNat_cube_add_one (q : ℕ) (hq : 1 ≤ q) :
    (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) = q ^ 3 + 1 := by
  have h1 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h1, Int.toNat_natCast]

private lemma toNat_four_sub_one (q : ℕ) (hq : 1 ≤ q) :
    (((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat) = q ^ 4 - 1 := by
  have h1 : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4) = ((q ^ 4 - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow 4 q (by omega))]
    push_cast
    ring
  rw [h1, Int.toNat_natCast]

private lemma toNat_five_add_one (q : ℕ) (hq : 1 ≤ q) :
    (((q : ℤ) ^ 5 - (-1 : ℤ) ^ 5).toNat) = q ^ 5 + 1 := by
  have h1 : ((q : ℤ) ^ 5 - (-1 : ℤ) ^ 5) = ((q ^ 5 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h1, Int.toNat_natCast]

private lemma dvd_div_of_coprime {a N g : ℕ} (hg : g ∣ N) (hcop : Nat.Coprime a g)
    (ha : a ∣ N) : a ∣ N / g := by
  have h : N = N / g * g := (Nat.div_mul_cancel hg).symm
  rw [h] at ha
  exact hcop.dvd_of_dvd_mul_right ha

private lemma pow_sub_one_ne_zero {q k : ℕ} (h2 : 2 ≤ q) (hk : k ≠ 0) : q ^ k - 1 ≠ 0 := by
  have h : 1 < q ^ k := Nat.one_lt_pow hk (by omega)
  omega

private lemma factorization_three_sq_sub_one_of_mod_three_eq_one {q : ℕ} (hq : q % 3 = 1)
    (h2 : 2 ≤ q) : (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 := by
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    change q ^ 2 - 1 ^ 2 = (q + 1) * (q - 1)
    rw [Nat.sq_sub_sq]
  rw [hfac, factorization_three_mul (by omega) (by omega),
    Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 3 ∣ q + 1), zero_add]

private lemma factorization_three_sq_sub_one_of_mod_three_eq_two {q : ℕ} (hq : q % 3 = 2) :
    (q ^ 2 - 1).factorization 3 = (q + 1).factorization 3 := by
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    change q ^ 2 - 1 ^ 2 = (q + 1) * (q - 1)
    rw [Nat.sq_sub_sq]
  rw [hfac, factorization_three_mul (by omega) (by omega),
    Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 3 ∣ q - 1), add_zero]

private lemma factorization_three_pow_four_sub_one {q : ℕ} (h3 : ¬ 3 ∣ q) (h2 : 2 ≤ q) :
    (q ^ 4 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 := by
  have h := factorization_three_pow_two_mul_sub_one (q := q) (m := 2) h3 h2 (by norm_num)
  rw [h, factorization_three_two, add_zero]

private lemma factorization_three_pow_six_sub_one {q : ℕ} (h3 : ¬ 3 ∣ q) (h2 : 2 ≤ q) :
    (q ^ 6 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + 1 := by
  have h := factorization_three_pow_two_mul_sub_one (q := q) (m := 3) h3 h2 (by norm_num)
  rw [h, factorization_three_three]

theorem factorization_three_pow_sq_sub_one {q f : ℕ} (hq : ¬ 3 ∣ q) (h2 : 2 ≤ q) (hf : f ≠ 0) :
    ((q ^ f) ^ 2 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + f.factorization 3 := by
  rw [← pow_mul, mul_comm]
  exact factorization_three_pow_two_mul_sub_one hq h2 hf

theorem factorization_three_two_pow_add_one {f : ℕ} (hf : Odd f) :
    (2 ^ f + 1).factorization 3 = 1 + f.factorization 3 := by
  have h := factorization_three_pow_add_one_of_mod_three_eq_two (q := 2) (k := f) (by norm_num) hf
  rw [Nat.Prime.factorization_self Nat.prime_three] at h
  linarith

theorem factorization_three_ordA_two {q : ℕ} (hq : q % 3 = 1) :
    (ordA 2 q).factorization 3 = 2 * (q - 1).factorization 3 := by
  rcases lt_or_eq_of_le (show 1 ≤ q by omega) with h2 | hq1
  · have h3 : ¬ 3 ∣ q := by omega
    have hd1 : 3 ∣ q - 1 := by omega
    have hg : Nat.gcd 3 (q - 1) = 3 := Nat.gcd_eq_left hd1
    have hB0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
    have hC0 : q ^ 3 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
    have hB : (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 :=
      factorization_three_sq_sub_one_of_mod_three_eq_one hq (by omega)
    have hC : (q ^ 3 - 1).factorization 3 = (q - 1).factorization 3 + 1 := by
      have h := factorization_three_pow_sub_one_of_mod_three_eq_one (q := q) (k := 3) hq
        (by omega) (by norm_num)
      rwa [factorization_three_three] at h
    have hA : (q ^ 3).factorization 3 = 0 := factorization_three_pow_of_not_dvd h3
    have hgq : 3 ∣ q ^ 2 - 1 := hd1.trans (pred_dvd_sq_sub_one q)
    have hdvd : 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hgq _) _
    have h1 : (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))).factorization 3 =
        (q ^ 3).factorization 3 + ((q ^ 2 - 1) * (q ^ 3 - 1)).factorization 3 :=
      factorization_three_mul (pow_ne_zero 3 (by omega)) (mul_ne_zero hB0 hC0)
    have h2' : ((q ^ 2 - 1) * (q ^ 3 - 1)).factorization 3 =
        (q ^ 2 - 1).factorization 3 + (q ^ 3 - 1).factorization 3 :=
      factorization_three_mul hB0 hC0
    have hN : (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))).factorization 3 =
        (q - 1).factorization 3 + ((q - 1).factorization 3 + 1) := by
      rw [h1, h2', hA, hB, hC]
      omega
    rw [ordA_two_eq, hg, Nat.factorization_div hdvd]
    change (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))).factorization 3 -
      (3 : ℕ).factorization 3 = 2 * (q - 1).factorization 3
    rw [hN, factorization_three_three]
    omega
  · obtain rfl : q = 1 := hq1.symm
    have hz : ordA 2 1 = 0 := by decide
    rw [hz]
    norm_num

theorem factorization_three_ordTwistedA_two {q : ℕ} (hq : q % 3 = 2) :
    (ordTwistedA 2 q).factorization 3 = 2 * (q + 1).factorization 3 := by
  have h2 : 2 ≤ q := by omega
  have h3 : ¬ 3 ∣ q := by omega
  have hd1 : 3 ∣ q + 1 := by omega
  have hg : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left hd1
  have ht2 : (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := toNat_sq_sub_one q (by omega)
  have ht3 : (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) = q ^ 3 + 1 := toNat_cube_add_one q (by omega)
  have hB0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hC0 : q ^ 3 + 1 ≠ 0 := by positivity
  have hB : (q ^ 2 - 1).factorization 3 = (q + 1).factorization 3 :=
    factorization_three_sq_sub_one_of_mod_three_eq_two hq
  have hC : (q ^ 3 + 1).factorization 3 = (q + 1).factorization 3 + 1 := by
    have h := factorization_three_pow_add_one_of_mod_three_eq_two (q := q) (k := 3) hq
      ⟨1, by norm_num⟩
    rwa [factorization_three_three] at h
  have hA : (q ^ 3).factorization 3 = 0 := factorization_three_pow_of_not_dvd h3
  have hgq : 3 ∣ q ^ 2 - 1 := hd1.trans (succ_dvd_sq_sub_one q)
  have hdvd : 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hgq _) _
  have h1 : (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))).factorization 3 =
      (q ^ 3).factorization 3 + ((q ^ 2 - 1) * (q ^ 3 + 1)).factorization 3 :=
    factorization_three_mul (pow_ne_zero 3 (by omega)) (mul_ne_zero hB0 hC0)
  have h2' : ((q ^ 2 - 1) * (q ^ 3 + 1)).factorization 3 =
      (q ^ 2 - 1).factorization 3 + (q ^ 3 + 1).factorization 3 :=
    factorization_three_mul hB0 hC0
  have hN : (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))).factorization 3 =
      (q + 1).factorization 3 + ((q + 1).factorization 3 + 1) := by
    rw [h1, h2', hA, hB, hC]
    omega
  rw [ordTwistedA_two_eq, ht2, ht3, hg, Nat.factorization_div hdvd]
  change (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))).factorization 3 -
    (3 : ℕ).factorization 3 = 2 * (q + 1).factorization 3
  rw [hN, factorization_three_three]
  omega

theorem factorization_three_ordA_three {q : ℕ} (hq : q % 3 = 2) :
    (ordA 3 q).factorization 3 = 2 * (q + 1).factorization 3 := by
  have h2 : 2 ≤ q := by omega
  have h3 : ¬ 3 ∣ q := by omega
  have hB0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hC0 : q ^ 3 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hD0 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hB : (q ^ 2 - 1).factorization 3 = (q + 1).factorization 3 :=
    factorization_three_sq_sub_one_of_mod_three_eq_two hq
  have hC : (q ^ 3 - 1).factorization 3 = 0 :=
    factorization_three_pow_sub_one_eq_zero_of_odd hq ⟨1, by norm_num⟩
  have hD : (q ^ 4 - 1).factorization 3 = (q + 1).factorization 3 := by
    rw [factorization_three_pow_four_sub_one h3 h2, hB]
  have hA : (q ^ 6).factorization 3 = 0 := factorization_three_pow_of_not_dvd h3
  have hg0 : (Nat.gcd 4 (q - 1)).factorization 3 = 0 :=
    factorization_three_gcd_eq_zero (by norm_num : ¬ 3 ∣ 4)
  have hgq : Nat.gcd 4 (q - 1) ∣ q ^ 2 - 1 :=
    (Nat.gcd_dvd_right 4 (q - 1)).trans (pred_dvd_sq_sub_one q)
  have hdvd : Nat.gcd 4 (q - 1) ∣ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgq _) _) _
  have h1 : (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1))).factorization 3 =
      (q ^ 6).factorization 3 + ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)).factorization 3 :=
    factorization_three_mul (pow_ne_zero 6 (by omega))
      (mul_ne_zero (mul_ne_zero hB0 hC0) hD0)
  have h2' : ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)).factorization 3 =
      ((q ^ 2 - 1) * (q ^ 3 - 1)).factorization 3 + (q ^ 4 - 1).factorization 3 :=
    factorization_three_mul (mul_ne_zero hB0 hC0) hD0
  have h3' : ((q ^ 2 - 1) * (q ^ 3 - 1)).factorization 3 =
      (q ^ 2 - 1).factorization 3 + (q ^ 3 - 1).factorization 3 :=
    factorization_three_mul hB0 hC0
  have hN : (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1))).factorization 3 =
      2 * (q + 1).factorization 3 := by
    rw [h1, h2', h3', hA, hB, hC, hD]
    omega
  rw [ordA_three_eq, Nat.factorization_div hdvd]
  change (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1))).factorization 3 -
    (Nat.gcd 4 (q - 1)).factorization 3 = 2 * (q + 1).factorization 3
  rw [hN, hg0]
  omega

theorem factorization_three_ordTwistedA_three {q : ℕ} (hq : q % 3 = 1) :
    (ordTwistedA 3 q).factorization 3 = 2 * (q - 1).factorization 3 := by
  rcases lt_or_eq_of_le (show 1 ≤ q by omega) with h2 | hq1
  · have h3 : ¬ 3 ∣ q := by omega
    have ht2 : (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := toNat_sq_sub_one q (by omega)
    have ht3 : (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) = q ^ 3 + 1 := toNat_cube_add_one q (by omega)
    have ht4 : (((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat) = q ^ 4 - 1 := toNat_four_sub_one q (by omega)
    have hB0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
    have hC0 : q ^ 3 + 1 ≠ 0 := by positivity
    have hD0 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
    have hB : (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 :=
      factorization_three_sq_sub_one_of_mod_three_eq_one hq (by omega)
    have hC : (q ^ 3 + 1).factorization 3 = 0 :=
      factorization_three_pow_add_one_eq_zero_of_mod_three_eq_one (k := 3) hq
    have hD : (q ^ 4 - 1).factorization 3 = (q - 1).factorization 3 := by
      rw [factorization_three_pow_four_sub_one h3 (by omega), hB]
    have hA : (q ^ 6).factorization 3 = 0 := factorization_three_pow_of_not_dvd h3
    have hg0 : (Nat.gcd 4 (q + 1)).factorization 3 = 0 :=
      factorization_three_gcd_eq_zero (by norm_num : ¬ 3 ∣ 4)
    have hgq : Nat.gcd 4 (q + 1) ∣ q ^ 2 - 1 :=
      (Nat.gcd_dvd_right 4 (q + 1)).trans (succ_dvd_sq_sub_one q)
    have hdvd : Nat.gcd 4 (q + 1) ∣
        q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgq _) _) _
    have h1 : (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))).factorization 3 =
        (q ^ 6).factorization 3 + ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)).factorization 3 :=
      factorization_three_mul (pow_ne_zero 6 (by omega))
        (mul_ne_zero (mul_ne_zero hB0 hC0) hD0)
    have h2' : ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)).factorization 3 =
        ((q ^ 2 - 1) * (q ^ 3 + 1)).factorization 3 + (q ^ 4 - 1).factorization 3 :=
      factorization_three_mul (mul_ne_zero hB0 hC0) hD0
    have h3' : ((q ^ 2 - 1) * (q ^ 3 + 1)).factorization 3 =
        (q ^ 2 - 1).factorization 3 + (q ^ 3 + 1).factorization 3 :=
      factorization_three_mul hB0 hC0
    have hN : (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))).factorization 3 =
        2 * (q - 1).factorization 3 := by
      rw [h1, h2', h3', hA, hB, hC, hD]
      omega
    rw [ordTwistedA_three_eq, ht2, ht3, ht4, Nat.factorization_div hdvd]
    change (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))).factorization 3 -
      (Nat.gcd 4 (q + 1)).factorization 3 = 2 * (q - 1).factorization 3
    rw [hN, hg0]
    omega
  · obtain rfl : q = 1 := hq1.symm
    have hz : ordTwistedA 3 1 = 0 := by decide
    rw [hz]
    norm_num

theorem factorization_three_ordA_four {q : ℕ} (hq : q % 3 = 2) :
    (ordA 4 q).factorization 3 = 2 * (q + 1).factorization 3 := by
  have h2 : 2 ≤ q := by omega
  have h3 : ¬ 3 ∣ q := by omega
  have hB0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hC0 : q ^ 3 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hD0 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hE0 : q ^ 5 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hB : (q ^ 2 - 1).factorization 3 = (q + 1).factorization 3 :=
    factorization_three_sq_sub_one_of_mod_three_eq_two hq
  have hC : (q ^ 3 - 1).factorization 3 = 0 :=
    factorization_three_pow_sub_one_eq_zero_of_odd hq ⟨1, by norm_num⟩
  have hD : (q ^ 4 - 1).factorization 3 = (q + 1).factorization 3 := by
    rw [factorization_three_pow_four_sub_one h3 h2, hB]
  have hE : (q ^ 5 - 1).factorization 3 = 0 :=
    factorization_three_pow_sub_one_eq_zero_of_odd hq ⟨2, by norm_num⟩
  have hA : (q ^ 10).factorization 3 = 0 := factorization_three_pow_of_not_dvd h3
  have hg0 : (Nat.gcd 5 (q - 1)).factorization 3 = 0 :=
    factorization_three_gcd_eq_zero (by norm_num : ¬ 3 ∣ 5)
  have hgq : Nat.gcd 5 (q - 1) ∣ q ^ 2 - 1 :=
    (Nat.gcd_dvd_right 5 (q - 1)).trans (pred_dvd_sq_sub_one q)
  have hdvd : Nat.gcd 5 (q - 1) ∣
      q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)) :=
    dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgq _) _) _) _
  have h1 : (q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1))).factorization 3 =
      (q ^ 10).factorization 3 +
        ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)).factorization 3 :=
    factorization_three_mul (pow_ne_zero 10 (by omega))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hB0 hC0) hD0) hE0)
  have h2' : ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)).factorization 3 =
      ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)).factorization 3 + (q ^ 5 - 1).factorization 3 :=
    factorization_three_mul (mul_ne_zero (mul_ne_zero hB0 hC0) hD0) hE0
  have h3' : ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)).factorization 3 =
      ((q ^ 2 - 1) * (q ^ 3 - 1)).factorization 3 + (q ^ 4 - 1).factorization 3 :=
    factorization_three_mul (mul_ne_zero hB0 hC0) hD0
  have h4' : ((q ^ 2 - 1) * (q ^ 3 - 1)).factorization 3 =
      (q ^ 2 - 1).factorization 3 + (q ^ 3 - 1).factorization 3 :=
    factorization_three_mul hB0 hC0
  have hN : (q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1))).factorization 3 =
      2 * (q + 1).factorization 3 := by
    rw [h1, h2', h3', h4', hA, hB, hC, hD, hE]
    omega
  rw [ordA_four_eq, Nat.factorization_div hdvd]
  change (q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1))).factorization 3 -
    (Nat.gcd 5 (q - 1)).factorization 3 = 2 * (q + 1).factorization 3
  rw [hN, hg0]
  omega

private lemma factorization_three_numer_twistedA_four {q : ℕ} (hq : q % 3 = 1) (h2 : 1 < q) :
    (q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1))).factorization 3 =
      2 * (q - 1).factorization 3 := by
  have h3 : ¬ 3 ∣ q := by omega
  have hB0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have hC0 : q ^ 3 + 1 ≠ 0 := by positivity
  have hD0 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have hE0 : q ^ 5 + 1 ≠ 0 := by positivity
  have hB : (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 :=
    factorization_three_sq_sub_one_of_mod_three_eq_one hq (by omega)
  have hC : (q ^ 3 + 1).factorization 3 = 0 :=
    factorization_three_pow_add_one_eq_zero_of_mod_three_eq_one (k := 3) hq
  have hD : (q ^ 4 - 1).factorization 3 = (q - 1).factorization 3 := by
    rw [factorization_three_pow_four_sub_one h3 (by omega), hB]
  have hE : (q ^ 5 + 1).factorization 3 = 0 :=
    factorization_three_pow_add_one_eq_zero_of_mod_three_eq_one (k := 5) hq
  have hA : (q ^ 10).factorization 3 = 0 := factorization_three_pow_of_not_dvd h3
  rw [factorization_three_mul (pow_ne_zero 10 (by omega))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hB0 hC0) hD0) hE0),
    factorization_three_mul (mul_ne_zero (mul_ne_zero hB0 hC0) hD0) hE0,
    factorization_three_mul (mul_ne_zero hB0 hC0) hD0, factorization_three_mul hB0 hC0,
    hA, hB, hC, hD, hE]
  omega

theorem factorization_three_ordTwistedA_four {q : ℕ} (hq : q % 3 = 1) :
    (ordTwistedA 4 q).factorization 3 = 2 * (q - 1).factorization 3 := by
  rcases lt_or_eq_of_le (show 1 ≤ q by omega) with h2 | hq1
  · have ht2 : (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := toNat_sq_sub_one q (by omega)
    have ht3 : (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) = q ^ 3 + 1 := toNat_cube_add_one q (by omega)
    have ht4 : (((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat) = q ^ 4 - 1 := toNat_four_sub_one q (by omega)
    have ht5 : (((q : ℤ) ^ 5 - (-1 : ℤ) ^ 5).toNat) = q ^ 5 + 1 := toNat_five_add_one q (by omega)
    have hg0 : (Nat.gcd 5 (q + 1)).factorization 3 = 0 :=
      factorization_three_gcd_eq_zero (by norm_num : ¬ 3 ∣ 5)
    have hgq : Nat.gcd 5 (q + 1) ∣ q ^ 2 - 1 :=
      (Nat.gcd_dvd_right 5 (q + 1)).trans (succ_dvd_sq_sub_one q)
    have hdvd : Nat.gcd 5 (q + 1) ∣
        q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)) :=
      dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgq _) _) _) _
    rw [ordTwistedA_four_eq, ht2, ht3, ht4, ht5, Nat.factorization_div hdvd]
    change (q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1))).factorization 3 -
      (Nat.gcd 5 (q + 1)).factorization 3 = 2 * (q - 1).factorization 3
    rw [factorization_three_numer_twistedA_four hq h2, hg0]
    omega
  · obtain rfl : q = 1 := hq1.symm
    have hz : ordTwistedA 4 1 = 0 := by decide
    rw [hz]
    norm_num

theorem factorization_three_ordBC_two {q : ℕ} (hq : ¬ 3 ∣ q) :
    (ordBC 2 q).factorization 3 = 2 * (q ^ 2 - 1).factorization 3 := by
  rcases lt_or_eq_of_le (show 1 ≤ q by omega) with h2 | hq1
  · have hB0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
    have hD0 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
    have hD : (q ^ 4 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 :=
      factorization_three_pow_four_sub_one hq (by omega)
    have hA : (q ^ 4).factorization 3 = 0 := factorization_three_pow_of_not_dvd hq
    have hg0 : (Nat.gcd 2 (q - 1)).factorization 3 = 0 :=
      factorization_three_gcd_eq_zero (by norm_num : ¬ 3 ∣ 2)
    have hgq : Nat.gcd 2 (q - 1) ∣ q ^ 2 - 1 :=
      (Nat.gcd_dvd_right 2 (q - 1)).trans (pred_dvd_sq_sub_one q)
    have hdvd : Nat.gcd 2 (q - 1) ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hgq _) _
    have h1 : (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))).factorization 3 =
        (q ^ 4).factorization 3 + ((q ^ 2 - 1) * (q ^ 4 - 1)).factorization 3 :=
      factorization_three_mul (pow_ne_zero 4 (by omega)) (mul_ne_zero hB0 hD0)
    have h2' : ((q ^ 2 - 1) * (q ^ 4 - 1)).factorization 3 =
        (q ^ 2 - 1).factorization 3 + (q ^ 4 - 1).factorization 3 :=
      factorization_three_mul hB0 hD0
    have hN : (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))).factorization 3 =
        2 * (q ^ 2 - 1).factorization 3 := by
      rw [h1, h2', hA, hD]
      omega
    rw [ordBC_two_eq, Nat.factorization_div hdvd]
    change (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))).factorization 3 -
      (Nat.gcd 2 (q - 1)).factorization 3 = 2 * (q ^ 2 - 1).factorization 3
    rw [hN, hg0]
    omega
  · obtain rfl : q = 1 := hq1.symm
    have hz : ordBC 2 1 = 0 := by decide
    rw [hz]
    norm_num

theorem factorization_three_ordG2 {q : ℕ} (hq : ¬ 3 ∣ q) (h2 : 2 ≤ q) :
    (ordG2 q).factorization 3 = 2 * (q ^ 2 - 1).factorization 3 + 1 := by
  have hB0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hC0 : q ^ 6 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hC : (q ^ 6 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + 1 :=
    factorization_three_pow_six_sub_one hq h2
  have hA : (q ^ 6).factorization 3 = 0 := factorization_three_pow_of_not_dvd hq
  have h1 : (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)).factorization 3 =
      (q ^ 6 * (q ^ 6 - 1)).factorization 3 + (q ^ 2 - 1).factorization 3 :=
    factorization_three_mul (mul_ne_zero (pow_ne_zero 6 (by omega)) hC0) hB0
  have h2' : (q ^ 6 * (q ^ 6 - 1)).factorization 3 =
      (q ^ 6).factorization 3 + (q ^ 6 - 1).factorization 3 :=
    factorization_three_mul (pow_ne_zero 6 (by omega)) hC0
  have hN : (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)).factorization 3 =
      2 * (q ^ 2 - 1).factorization 3 + 1 := by
    rw [h1, h2', hA, hC]
    omega
  have hord : ordG2 q = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := rfl
  rw [hord, hN]

theorem factorization_three_ordTrialityD4 {q : ℕ} (hq : ¬ 3 ∣ q) (h2 : 2 ≤ q) :
    (ordTrialityD4 q).factorization 3 = 2 * (q ^ 2 - 1).factorization 3 + 2 := by
  have hB0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hC0 : q ^ 6 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hD0 : q ^ 8 + q ^ 4 + 1 ≠ 0 := by positivity
  have hC : (q ^ 6 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + 1 :=
    factorization_three_pow_six_sub_one hq h2
  have hD : (q ^ 8 + q ^ 4 + 1).factorization 3 = 1 :=
    factorization_three_pow_eight_add_pow_four_add_one hq h2
  have hA : (q ^ 12).factorization 3 = 0 := factorization_three_pow_of_not_dvd hq
  have h1 : (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)).factorization 3 =
      (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1)).factorization 3 +
        (q ^ 2 - 1).factorization 3 :=
    factorization_three_mul
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 12 (by omega)) hD0) hC0) hB0
  have h2' : (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1)).factorization 3 =
      (q ^ 12 * (q ^ 8 + q ^ 4 + 1)).factorization 3 + (q ^ 6 - 1).factorization 3 :=
    factorization_three_mul (mul_ne_zero (pow_ne_zero 12 (by omega)) hD0) hC0
  have h3' : (q ^ 12 * (q ^ 8 + q ^ 4 + 1)).factorization 3 =
      (q ^ 12).factorization 3 + (q ^ 8 + q ^ 4 + 1).factorization 3 :=
    factorization_three_mul (pow_ne_zero 12 (by omega)) hD0
  have hN : (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)).factorization 3 =
      2 * (q ^ 2 - 1).factorization 3 + 2 := by
    rw [h1, h2', h3', hA, hD, hC]
    omega
  have hord : ordTrialityD4 q = q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := rfl
  rw [hord, hN]

theorem factorization_three_ordTwistedF4 {q : ℕ} (hq : q % 3 = 2) :
    (ordTwistedF4 q).factorization 3 = 2 * (q + 1).factorization 3 + 1 := by
  have h2 : 2 ≤ q := by omega
  have h3 : ¬ 3 ∣ q := by omega
  have hB0 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
  have hC0 : q ^ 3 + 1 ≠ 0 := by positivity
  have hD0 : q ^ 6 + 1 ≠ 0 := by positivity
  have hE0 : q - 1 ≠ 0 := by omega
  have hB : (q ^ 4 - 1).factorization 3 = (q + 1).factorization 3 := by
    rw [factorization_three_pow_four_sub_one h3 h2,
      factorization_three_sq_sub_one_of_mod_three_eq_two hq]
  have hC : (q ^ 3 + 1).factorization 3 = (q + 1).factorization 3 + 1 := by
    have h := factorization_three_pow_add_one_of_mod_three_eq_two (q := q) (k := 3) hq
      ⟨1, by norm_num⟩
    rwa [factorization_three_three] at h
  have hD : (q ^ 6 + 1).factorization 3 = 0 :=
    factorization_three_pow_add_one_eq_zero_of_even h3 ⟨3, by norm_num⟩
  have hE : (q - 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 3 ∣ q - 1)
  have hA : (q ^ 12).factorization 3 = 0 := factorization_three_pow_of_not_dvd h3
  have h1 : (q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)).factorization 3 =
      (q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1)).factorization 3 +
        (q - 1).factorization 3 :=
    factorization_three_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 12 (by omega)) hD0) hB0) hC0) hE0
  have h2' : (q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1)).factorization 3 =
      (q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1)).factorization 3 + (q ^ 3 + 1).factorization 3 :=
    factorization_three_mul
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 12 (by omega)) hD0) hB0) hC0
  have h3' : (q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1)).factorization 3 =
      (q ^ 12 * (q ^ 6 + 1)).factorization 3 + (q ^ 4 - 1).factorization 3 :=
    factorization_three_mul (mul_ne_zero (pow_ne_zero 12 (by omega)) hD0) hB0
  have h4' : (q ^ 12 * (q ^ 6 + 1)).factorization 3 =
      (q ^ 12).factorization 3 + (q ^ 6 + 1).factorization 3 :=
    factorization_three_mul (pow_ne_zero 12 (by omega)) hD0
  have hN : (q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)).factorization 3 =
      2 * (q + 1).factorization 3 + 1 := by
    rw [h1, h2', h3', h4', hA, hD, hB, hC, hE]
    omega
  have hord : ordTwistedF4 q = q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) := rfl
  rw [hord, hN]

theorem eightyone_dvd_ordBC_two {q : ℕ} (hq : 3 ∣ q) : 81 ∣ ordBC 2 q := by
  obtain ⟨k, rfl⟩ := hq
  rcases eq_or_lt_of_le (Nat.zero_le k) with hk | hk
  · subst hk
    have hz : ordBC 2 (3 * 0) = 0 := by decide
    rw [hz]
    exact dvd_zero 81
  · have h2 : 2 ≤ 3 * k := by omega
    have h81 : 81 ∣ (3 * k) ^ 4 := by
      rw [mul_pow]
      exact ⟨k ^ 4, by norm_num⟩
    have hB0 : (3 * k) ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
    have hD0 : (3 * k) ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero h2 (by norm_num)
    have hN : 81 ∣ (3 * k) ^ 4 * (((3 * k) ^ 2 - 1) * ((3 * k) ^ 4 - 1)) :=
      dvd_mul_of_dvd_left h81 _
    have hgq : Nat.gcd 2 (3 * k - 1) ∣ (3 * k) ^ 2 - 1 :=
      (Nat.gcd_dvd_right 2 (3 * k - 1)).trans (pred_dvd_sq_sub_one (3 * k))
    have hgN : Nat.gcd 2 (3 * k - 1) ∣
        (3 * k) ^ 4 * (((3 * k) ^ 2 - 1) * ((3 * k) ^ 4 - 1)) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hgq _) _
    have hg2 : Nat.gcd 2 (3 * k - 1) ∣ 2 := Nat.gcd_dvd_left 2 (3 * k - 1)
    have hcop : Nat.Coprime 81 (Nat.gcd 2 (3 * k - 1)) :=
      Nat.Coprime.coprime_dvd_right hg2 (by norm_num : Nat.Coprime 81 2)
    rw [ordBC_two_eq]
    exact dvd_div_of_coprime hgN hcop hN

theorem eightyone_dvd_ordG2 {q : ℕ} (hq : 3 ∣ q) : 81 ∣ ordG2 q := by
  have h81 : 81 ∣ q ^ 4 := by
    obtain ⟨k, rfl⟩ := hq
    rw [mul_pow]
    exact ⟨k ^ 4, by norm_num⟩
  have hq6 : 81 ∣ q ^ 6 := h81.trans (Nat.pow_dvd_pow q (by norm_num : 4 ≤ 6))
  have hord : ordG2 q = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := rfl
  rw [hord]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hq6 _) _

theorem eightyone_dvd_ordTrialityD4 {q : ℕ} (hq : 3 ∣ q) : 81 ∣ ordTrialityD4 q := by
  have h81 : 81 ∣ q ^ 4 := by
    obtain ⟨k, rfl⟩ := hq
    rw [mul_pow]
    exact ⟨k ^ 4, by norm_num⟩
  have hq12 : 81 ∣ q ^ 12 := h81.trans (Nat.pow_dvd_pow q (by norm_num : 4 ≤ 12))
  have hord : ordTrialityD4 q =
      q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := rfl
  rw [hord]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hq12 _) _) _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
