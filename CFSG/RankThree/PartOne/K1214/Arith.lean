module

public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.RankThree.PartOne.K1214

theorem exists_pow_mul {p N : ℕ} (hp : p.Prime) (hN : N ≠ 0) :
    ∃ m, N = p ^ padicValNat p N * m ∧ ¬ p ∣ m := by
  refine ⟨N / p ^ padicValNat p N, ?_, ?_⟩
  · rw [← Nat.factorization_def N hp]
    exact (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  · rw [← Nat.factorization_def N hp]
    exact Nat.not_dvd_ordCompl hp hN

theorem lte_minus {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 1 ≤ g) (hdvd : p ∣ 2 ^ g - 1) :
    ∃ e m m' : ℕ, 2 ≤ e ∧ 2 ^ g - 1 = p ^ (e - 1) * m' ∧ ¬ p ∣ m' ∧
      2 ^ (p * g) - 1 = p ^ e * m ∧ ¬ p ∣ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h2g : 1 < 2 ^ g := Nat.one_lt_two_pow (by omega)
  have hN0 : 2 ^ g - 1 ≠ 0 := by omega
  have hpx : ¬ p ∣ 2 ^ g := fun h => by
    have h1 : p ∣ 2 ^ g - (2 ^ g - 1) := Nat.dvd_sub h hdvd
    rw [Nat.sub_sub_self (by omega : 1 ≤ 2 ^ g)] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have he1 : 1 ≤ padicValNat p (2 ^ g - 1) := one_le_padicValNat_of_dvd hN0 hdvd
  obtain ⟨m', hm'1, hm'2⟩ := exists_pow_mul hp hN0
  have hv : padicValNat p (2 ^ (p * g) - 1) = padicValNat p (2 ^ g - 1) + 1 := by
    have h := padicValNat.pow_sub_pow (p := p) hodd (x := 2 ^ g) (y := 1) h2g
      (by simpa using hdvd) hpx hp.ne_zero
    rw [one_pow, ← pow_mul, mul_comm g p, padicValNat_self] at h
    simpa using h
  have hN1 : 2 ^ (p * g) - 1 ≠ 0 := by
    have : 1 < 2 ^ (p * g) := Nat.one_lt_two_pow (Nat.mul_ne_zero hp.ne_zero (by omega))
    omega
  obtain ⟨m, hm1, hm2⟩ := exists_pow_mul hp hN1
  refine ⟨padicValNat p (2 ^ g - 1) + 1, m, m', by omega, ?_, hm'2, ?_, hm2⟩
  · rw [Nat.add_sub_cancel]
    exact hm'1
  · rw [← hv]
    exact hm1

theorem lte_plus {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ g + 1) :
    ∃ e m m' : ℕ, 2 ≤ e ∧ 2 ^ g + 1 = p ^ (e - 1) * m' ∧ ¬ p ∣ m' ∧
      2 ^ (p * g) + 1 = p ^ e * m ∧ ¬ p ∣ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hN0 : 2 ^ g + 1 ≠ 0 := Nat.succ_ne_zero _
  have hpx : ¬ p ∣ 2 ^ g := fun h => by
    have h1 : p ∣ 1 := (Nat.dvd_add_right h).1 hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have he1 : 1 ≤ padicValNat p (2 ^ g + 1) := one_le_padicValNat_of_dvd hN0 hdvd
  obtain ⟨m', hm'1, hm'2⟩ := exists_pow_mul hp hN0
  have hv : padicValNat p (2 ^ (p * g) + 1) = padicValNat p (2 ^ g + 1) + 1 := by
    have h := padicValNat.pow_add_pow (p := p) hodd (x := 2 ^ g) (y := 1) (by simpa using hdvd) hpx
      hodd
    rw [one_pow, ← pow_mul, mul_comm g p, padicValNat_self] at h
    simpa using h
  have hN1 : 2 ^ (p * g) + 1 ≠ 0 := Nat.succ_ne_zero _
  obtain ⟨m, hm1, hm2⟩ := exists_pow_mul hp hN1
  refine ⟨padicValNat p (2 ^ g + 1) + 1, m, m', by omega, ?_, hm'2, ?_, hm2⟩
  · rw [Nat.add_sub_cancel]
    exact hm'1
  · rw [← hv]
    exact hm1

end CFSG.RankThree.PartOne.K1214
