module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Trv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c1_G47_inverted_prime {Hs : Type} [Group Hs] [Finite Hs] {N : Subgroup Hs}
    (hN : N.Normal) (hNodd : Odd (Nat.card N)) {v : Hs} (hv : v * v = 1)
    (hvc : ∃ n ∈ N, v * n ≠ n * v) :
    ∃ (q : ℕ) (n : Hs), q.Prime ∧ q ≠ 2 ∧ n ∈ N ∧ orderOf n = q ∧ v * n * v⁻¹ = n⁻¹ := by
  obtain ⟨n₀, hn₀, hne⟩ := hvc
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hvv : v⁻¹ * v⁻¹ = 1 := by rw [← mul_inv_rev, hv, inv_one]
  set m : Hs := n₀⁻¹ * (v * n₀ * v⁻¹) with hm
  have hmN : m ∈ N := N.mul_mem (N.inv_mem hn₀) (hN.conj_mem n₀ hn₀ v)
  have hm1 : m ≠ 1 := by
    intro h
    apply hne
    have h1 : v * n₀ * v⁻¹ = n₀ := by
      rw [hm] at h
      exact (inv_mul_eq_one.1 h).symm
    calc v * n₀ = v * n₀ * v⁻¹ * v := by group
      _ = n₀ * v := by rw [h1]
  have hvm : v * m * v⁻¹ = m⁻¹ := by
    have h1 : v * m * v⁻¹ = v * n₀⁻¹ * v * n₀ * (v⁻¹ * v⁻¹) := by rw [hm, hvi]; group
    have h2 : m⁻¹ = v * n₀⁻¹ * v⁻¹ * n₀ := by rw [hm]; group
    rw [h1, h2, hvv, mul_one, hvi]
  have hodd : Odd (orderOf m) := hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hmN)
  have hne1 : orderOf m ≠ 1 := fun h => hm1 (orderOf_eq_one_iff.1 h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne1
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨j, hj⟩ := hqd
    omega
  refine ⟨q, m ^ (orderOf m / q), hq, hq2, N.pow_mem hmN _, ?_, ?_⟩
  · exact orderOf_pow_orderOf_div (orderOf_pos m).ne' hqd
  · rw [← conj_pow, hvm, inv_pow]

theorem s16c1_G47_caseB {Hs : Type} [Group Hs] [Finite Hs] {Vs N : Subgroup Hs} (hN : N.Normal)
    (hNodd : Odd (Nat.card N)) (hV2 : ∀ v ∈ Vs, v * v = 1)
    (hVN : ∀ v ∈ Vs, (∀ n ∈ N, v * n = n * v) → v = 1) (h3 : ¬ 3 ∣ Nat.card N)
    {E : Type} [Group E] (hE : ∀ e : E, e * e = 1) (ρ : Hs →* MulAut E) {a : E} (ha : a ≠ 1)
    (hT : ∀ v ∈ Vs, ∀ e : E, ρ v e = e ∨ ρ v e = e * a)
    (hstab : ∀ r : Hs, ρ r a = a → ∀ v ∈ Vs, r * v * r⁻¹ ∈ Vs)
    (hα : ∃ v ∈ Vs, ρ v ≠ 1) : False := by
  obtain ⟨v, hvV, hρv⟩ := hα
  by_cases hvc : ∀ n ∈ N, v * n = n * v
  · exact hρv (by rw [hVN v hvV hvc, map_one])
  · push Not at hvc
    obtain ⟨q, n, hq, hq2, hnN, hord, hinv⟩ :=
      s16c1_G47_inverted_prime hN hNodd (hV2 v hvV) hvc
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hV2 v hvV)
    have hvn : v * n = n⁻¹ * v := by
      rw [hvi] at hinv
      calc v * n = v * n * v * v := by rw [mul_assoc (v * n) v v, hV2 v hvV, mul_one]
        _ = n⁻¹ * v := by rw [hinv]
    have hvv' : v * (n * v * n⁻¹) = n⁻¹ * n⁻¹ := by
      calc v * (n * v * n⁻¹) = (v * n) * v * n⁻¹ := by group
        _ = n⁻¹ * (v * v) * n⁻¹ := by rw [hvn]; group
        _ = n⁻¹ * n⁻¹ := by rw [hV2 v hvV]; group
    by_cases hna : ρ n a = a
    · have hv' : n * v * n⁻¹ ∈ Vs := hstab n hna v hvV
      have hprod : v * (n * v * n⁻¹) ∈ Vs := Vs.mul_mem hvV hv'
      have h2 := hV2 _ hprod
      rw [hvv'] at h2
      have h4 : n ^ 4 = 1 := by
        have : n ^ 4 = (n⁻¹ * n⁻¹ * (n⁻¹ * n⁻¹))⁻¹ := by group
        rw [this, h2, inv_one]
      have hdvd : q ∣ 2 ^ 2 := by
        have h5 : q ∣ 4 := hord ▸ orderOf_dvd_of_pow_eq_one h4
        simpa using h5
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd))
    · have hρρ : ∀ e : E, ρ n (ρ n⁻¹ e) = e := fun e => by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      have hb1 : ρ n a ≠ 1 := by
        intro h
        apply ha
        have h2 := congrArg (ρ n⁻¹) h
        rw [map_one] at h2
        rw [← h2, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      have hab : a ≠ ρ n a := fun h => hna h.symm
      have hσ : ∀ x, ρ v x = x ∨ ρ v x = x * a := hT v hvV
      have hτ : ∀ x, ρ (n * v * n⁻¹) x = x ∨ ρ (n * v * n⁻¹) x = x * ρ n a := by
        intro x
        have hτx : ρ (n * v * n⁻¹) x = ρ n (ρ v (ρ n⁻¹ x)) := by
          simp only [map_mul, MulAut.mul_apply]
        rcases hT v hvV (ρ n⁻¹ x) with h | h
        · left
          rw [hτx, h, hρρ]
        · right
          rw [hτx, h, map_mul, hρρ]
      have hτ1 : ρ (n * v * n⁻¹) ≠ 1 := by
        intro h
        apply hρv
        have h2 : ρ v = ρ n⁻¹ * ρ (n * v * n⁻¹) * ρ n := by
          rw [← map_mul, ← map_mul]
          congr 1
          group
        rw [h2, h, mul_one, ← map_mul, inv_mul_cancel, map_one]
      have h234 := s16c1_G47_two_transv hE ha hb1 hab hσ hτ hρv hτ1
      have hnq : n ^ q = 1 := hord ▸ pow_orderOf_eq_one n
      have hpow : (n⁻¹ * n⁻¹) ^ q = 1 := by
        have h1 : n⁻¹ * n⁻¹ = (n ^ 2)⁻¹ := by group
        rw [h1, inv_pow, ← pow_mul, mul_comm 2 q, pow_mul, hnq, one_pow, inv_one]
      have hdvd : orderOf (ρ v * ρ (n * v * n⁻¹)) ∣ q := by
        rw [← map_mul, hvv']
        calc orderOf (ρ (n⁻¹ * n⁻¹)) ∣ orderOf (n⁻¹ * n⁻¹) := orderOf_map_dvd ρ _
          _ ∣ q := orderOf_dvd_of_pow_eq_one hpow
      have hq3 : q = 3 := by
        rcases h234 with h | h | h <;> rw [h] at hdvd
        · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hdvd).symm hq2
        · exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hdvd).symm
        · have h2 : 2 ∣ q := Nat.dvd_trans (by norm_num) hdvd
          exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h2).symm hq2
      apply h3
      rw [← hq3, ← hord]
      exact Subgroup.orderOf_dvd_natCard N hnN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
