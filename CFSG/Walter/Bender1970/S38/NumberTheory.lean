module

public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.Walter

theorem add_two_le_two_pow {b : ℕ} (hb : 2 ≤ b) : b + 2 ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem two_mul_add_two_le_two_pow {b : ℕ} (hb : 3 ≤ b) : 2 * b + 2 ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem eq_one_and_eq_two_of_two_pow_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b)
    (h : 2 ^ a * 2 ^ b = (2 ^ a) ^ (2 ^ b - 1)) : a = 1 ∧ b = 2 := by
  rw [← pow_add, ← pow_mul] at h
  have h' : a + b = a * (2 ^ b - 1) := Nat.pow_right_injective le_rfl h
  have hb2 := add_two_le_two_pow hb
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ b - 1 = b + 1 + m := ⟨2 ^ b - 1 - (b + 1), by omega⟩
  rw [hm] at h'
  have ha1 : a = 1 := by
    by_contra hne
    have ha2 : 2 ≤ a := by omega
    nlinarith
  subst ha1
  refine ⟨rfl, ?_⟩
  by_contra hne
  have := two_mul_add_two_le_two_pow (show 3 ≤ b by omega)
  omega

theorem eq_two_and_eq_four_of_mul_eq_pow {w q : ℕ} (hw : ∃ a, w = 2 ^ a) (hq : ∃ b, q = 2 ^ b)
    (hw2 : 2 ≤ w) (hq4 : 4 ≤ q) (h : w * q = w ^ (q - 1)) : w = 2 ∧ q = 4 := by
  obtain ⟨a, rfl⟩ := hw
  obtain ⟨b, rfl⟩ := hq
  have ha : 1 ≤ a := by
    by_contra h0
    rw [show a = 0 by omega] at hw2
    norm_num at hw2
  have hb : 2 ≤ b := by
    by_contra h0
    have : 2 ^ b ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨rfl, rfl⟩ := eq_one_and_eq_two_of_two_pow_mul ha hb h
  norm_num

theorem sub_one_mul_add_one_lt_pow {x m : ℕ} (hx : 2 ≤ x) (hm : 2 ≤ m) :
    (x - 1) * m + 1 < x ^ m := by
  induction m, hm using Nat.le_induction with
  | base =>
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 := ⟨x - 2, by omega⟩
    have h1 : (y + 2 - 1) = y + 1 := by omega
    rw [h1, pow_two]
    nlinarith
  | succ n hn ih =>
    rw [pow_succ]
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 := ⟨x - 2, by omega⟩
    have h1 : (y + 2 - 1) = y + 1 := by omega
    rw [h1] at ih ⊢
    have h2 : ((y + 1) * n + 2) * (y + 2) ≤ (y + 2) ^ n * (y + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith [h2, Nat.zero_le (y * y * n), Nat.zero_le (y * n), Nat.zero_le n, Nat.zero_le y]

theorem false_of_ordCompl_dvd {ℓ f c : ℕ} (hℓ : ℓ.Prime) (hc : 1 ≤ c) (hcf : c < f)
    (hdvd : ℓ ∣ 2 ^ f - 2 ^ c) (h : ordCompl[ℓ] (2 ^ f - 1) ∣ 2 ^ c - 1) : False := by
  have hfc : 2 ^ c < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) hcf
  have hc1 : 2 ≤ 2 ^ c := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
  set n := 2 ^ f - 1 with hn
  have hn0 : n ≠ 0 := by omega
  have hℓn : ℓ ∣ n := by
    by_contra hnd
    have h0 : n.factorization ℓ = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
    rw [h0, pow_zero, Nat.div_one] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hn_odd : Odd n := by
    have h2f : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    rw [hn]
    exact Nat.Even.sub_odd (by omega) h2f odd_one
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hn_odd) (even_iff_two_dvd.mpr hℓn)
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hfc' : 2 ^ f - 2 ^ c = 2 ^ c * (2 ^ (f - c) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hcf.le]
  have hℓ2c : Nat.Coprime ℓ (2 ^ c) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hℓ Nat.prime_two).mpr hℓ2)
  have hℓfc : ℓ ∣ 2 ^ (f - c) - 1 := by
    rw [hfc'] at hdvd
    exact hℓ2c.dvd_of_dvd_mul_left hdvd
  set d := Nat.gcd f c with hd
  have hgcd1 : Nat.gcd f (f - c) = d := by
    rw [hd, Nat.gcd_self_sub_right hcf.le]
  have hℓd : ℓ ∣ 2 ^ d - 1 := by
    rw [← hgcd1, ← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd hℓn hℓfc
  have hcompl : ordCompl[ℓ] n ∣ 2 ^ d - 1 := by
    rw [hd, ← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd (Nat.ordCompl_dvd n ℓ) h
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right f (by omega)
  have hdf : d ∣ f := Nat.gcd_dvd_left f c
  have hdc : d ≤ c := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right f c)
  obtain ⟨m, hm⟩ := hdf
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m <;> simp at hm <;> omega
    · exact hge
  have h2d : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd0
  have hnpow : n = (2 ^ d) ^ m - 1 ^ m := by rw [one_pow, ← pow_mul, ← hm]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2d : ¬ ℓ ∣ 2 ^ d := fun h' =>
    hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h'))
  have hlte : padicValNat ℓ n = padicValNat ℓ (2 ^ d - 1) + padicValNat ℓ m := by
    rw [hnpow]
    exact padicValNat.pow_sub_pow hℓodd (by omega) hℓd hℓ2d (by omega)
  have hd1 : 2 ^ d - 1 ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  rw [← Nat.factorization_def n hℓ, ← Nat.factorization_def _ hℓ,
    ← Nat.factorization_def m hℓ] at hlte
  have hcop : Nat.Coprime (ordCompl[ℓ] n) (ordProj[ℓ] (2 ^ d - 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_ordCompl hℓ hn0).symm
  have hcompl' : ordCompl[ℓ] n ∣ ordCompl[ℓ] (2 ^ d - 1) := by
    have h1 := hcompl
    rw [← Nat.ordProj_mul_ordCompl_eq_self (2 ^ d - 1) ℓ] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  have hle1 : ordCompl[ℓ] n ≤ ordCompl[ℓ] (2 ^ d - 1) :=
    Nat.le_of_dvd (Nat.ordCompl_pos ℓ hd1) hcompl'
  have hle2 : ordProj[ℓ] m ≤ m := Nat.ordProj_le ℓ hm0
  have hn_eq : n = ordProj[ℓ] (2 ^ d - 1) * ordProj[ℓ] m * ordCompl[ℓ] n := by
    rw [← pow_add, ← hlte, Nat.ordProj_mul_ordCompl_eq_self]
  have hbound : n ≤ (2 ^ d - 1) * m :=
    calc n = ordProj[ℓ] (2 ^ d - 1) * ordProj[ℓ] m * ordCompl[ℓ] n := hn_eq
      _ ≤ ordProj[ℓ] (2 ^ d - 1) * m * ordCompl[ℓ] (2 ^ d - 1) := by gcongr
      _ = (2 ^ d - 1) * m := by rw [mul_right_comm, Nat.ordProj_mul_ordCompl_eq_self]
  have hlt := sub_one_mul_add_one_lt_pow h2d hm2
  rw [← pow_mul, ← hm] at hlt
  omega

end CFSG.Walter
