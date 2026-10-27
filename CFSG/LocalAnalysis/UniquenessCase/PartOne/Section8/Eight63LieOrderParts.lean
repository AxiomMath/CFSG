module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (ordTrialityD4 ordTwistedF4)

theorem factorization_ordTwistedF4_of_dvd_sub_one {q r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hq : 2 ≤ q) (hrd : r ∣ q - 1) :
    (ordTwistedF4 q).factorization r = 2 * (q - 1).factorization r := by
  have hq1 : 1 ≤ q := by omega
  have hr2 : r ≠ 2 := by omega
  have hr3ne : r ≠ 3 := by omega
  have hq0 : q ≠ 0 := by omega
  have hqm1 : q - 1 ≠ 0 := by omega
  have hqp1 : q + 1 ≠ 0 := by omega
  have hq12 : q ^ 12 ≠ 0 := pow_ne_zero _ hq0
  have h6p1nz : q ^ 6 + 1 ≠ 0 := by
    have h6 : 0 < q ^ 6 := pow_pos (by omega) 6
    omega
  have h2p1nz : q ^ 2 + 1 ≠ 0 := by
    have h2 : 0 < q ^ 2 := pow_pos (by omega) 2
    omega
  have h2mq1eq : q ^ 2 - q + 1 = q * (q - 1) + 1 := by
    obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hsq : (w + 1) ^ 2 - (w + 1) = (w + 1) * w := by
      have h' : (w + 1) ^ 2 = (w + 1) * w + (w + 1) := by ring
      omega
    rw [hsq]
  have h2mq1nz : q ^ 2 - q + 1 ≠ 0 := by
    rw [h2mq1eq]
    omega
  have hrdq : ¬ r ∣ q := by
    intro h
    have h1d : r ∣ 1 := by
      have h' := Nat.dvd_sub h hrd
      have e : q - (q - 1) = 1 := by omega
      rwa [e] at h'
    exact hr.ne_one (Nat.dvd_one.mp h1d)
  have hrdp1 : ¬ r ∣ q + 1 := by
    intro h
    have h2d : r ∣ 2 := by
      have h' := Nat.dvd_sub h hrd
      have e : q + 1 - (q - 1) = 2 := by omega
      rwa [e] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2d)
  have hrd2p1 : ¬ r ∣ q ^ 2 + 1 := by
    intro h
    have hd2 : r ∣ q ^ 2 - 1 := hrd.trans (Nat.sub_one_dvd_pow_sub_one q 2)
    have h2d : r ∣ 2 := by
      have h' := Nat.dvd_sub h hd2
      have e : q ^ 2 + 1 - (q ^ 2 - 1) = 2 := by
        have h2' : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
        omega
      rwa [e] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2d)
  have hrd6p1 : ¬ r ∣ q ^ 6 + 1 := by
    intro h
    have hd6 : r ∣ q ^ 6 - 1 := hrd.trans (Nat.sub_one_dvd_pow_sub_one q 6)
    have h2d : r ∣ 2 := by
      have h' := Nat.dvd_sub h hd6
      have e : q ^ 6 + 1 - (q ^ 6 - 1) = 2 := by
        have h6' : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
        omega
      rwa [e] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2d)
  have hrd2mq1 : ¬ r ∣ q ^ 2 - q + 1 := by
    intro h
    rw [h2mq1eq] at h
    have hdiv : r ∣ q * (q - 1) := dvd_mul_of_dvd_right hrd q
    have h1d : r ∣ 1 := by
      have h' := Nat.dvd_sub h hdiv
      simpa using h'
    exact hr.ne_one (Nat.dvd_one.mp h1d)
  have h4 : q ^ 4 - 1 = (q - 1) * (q + 1) * (q ^ 2 + 1) := by
    obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  have h3 : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    obtain ⟨w, rfl⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
    have hsq : (w + 1) ^ 2 - (w + 1) = (w + 1) * w := by
      have h' : (w + 1) ^ 2 = (w + 1) * w + (w + 1) := by ring
      omega
    rw [hsq]
    ring
  have hqfac : (q ^ 12).factorization r = 0 := by
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hrdq, mul_zero]
  have t1 : (q ^ 12 * (q ^ 6 + 1)).factorization r = 0 := by
    rw [Nat.factorization_mul hq12 h6p1nz, Finsupp.add_apply, hqfac,
      Nat.factorization_eq_zero_of_not_dvd hrd6p1, add_zero]
  have u1 : ((q - 1) * (q + 1)).factorization r = (q - 1).factorization r := by
    rw [Nat.factorization_mul hqm1 hqp1, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hrdp1, add_zero]
  have t2 : ((q - 1) * (q + 1) * (q ^ 2 + 1)).factorization r =
      (q - 1).factorization r := by
    rw [Nat.factorization_mul (mul_ne_zero hqm1 hqp1) h2p1nz, Finsupp.add_apply, u1,
      Nat.factorization_eq_zero_of_not_dvd hrd2p1, add_zero]
  have t3 : ((q + 1) * (q ^ 2 - q + 1)).factorization r = 0 := by
    rw [Nat.factorization_mul hqp1 h2mq1nz, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hrdp1,
      Nat.factorization_eq_zero_of_not_dvd hrd2mq1, add_zero]
  have t4 : ((q ^ 12 * (q ^ 6 + 1)) * ((q - 1) * (q + 1) * (q ^ 2 + 1))).factorization r =
      (q - 1).factorization r := by
    rw [Nat.factorization_mul (mul_ne_zero hq12 h6p1nz)
      (mul_ne_zero (mul_ne_zero hqm1 hqp1) h2p1nz), Finsupp.add_apply, t1, t2, zero_add]
  have t5 : (((q ^ 12 * (q ^ 6 + 1)) * ((q - 1) * (q + 1) * (q ^ 2 + 1))) *
      ((q + 1) * (q ^ 2 - q + 1))).factorization r = (q - 1).factorization r := by
    rw [Nat.factorization_mul
      (mul_ne_zero (mul_ne_zero hq12 h6p1nz) (mul_ne_zero (mul_ne_zero hqm1 hqp1) h2p1nz))
      (mul_ne_zero hqp1 h2mq1nz), Finsupp.add_apply, t4, t3, add_zero]
  have t6 : ((((q ^ 12 * (q ^ 6 + 1)) * ((q - 1) * (q + 1) * (q ^ 2 + 1))) *
      ((q + 1) * (q ^ 2 - q + 1))) * (q - 1)).factorization r =
      2 * (q - 1).factorization r := by
    rw [Nat.factorization_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hq12 h6p1nz)
        (mul_ne_zero (mul_ne_zero hqm1 hqp1) h2p1nz)) (mul_ne_zero hqp1 h2mq1nz)) hqm1,
      Finsupp.add_apply, t5]
    omega
  unfold ordTwistedF4
  rw [h4, h3]
  exact t6

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
