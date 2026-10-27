module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Order
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open Polynomial

theorem two_pow_succ_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (t : ℕ) :
    2 ^ (t + 1) ∣ p ^ 2 ^ t - 1 := by
  have hcop : Nat.Coprime p (2 ^ (t + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hodd)
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime_pow_succ Nat.prime_two] at h
  simp only [Nat.add_one_sub_one, mul_one] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).1 h.symm

theorem exists_isPrimitiveRoot_galoisField (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (t : ℕ) :
    ∃ ζ : GaloisField p (2 ^ t), IsPrimitiveRoot ζ (2 ^ (t + 1)) := by
  refine CFSG.HardMathSupport.Curtis.Coordinator.exists_primitiveRoot_of_dvd ?_
  rw [GaloisField.card p (2 ^ t) (pow_ne_zero _ two_ne_zero)]
  exact two_pow_succ_dvd_pow_sub_one Fact.out hodd t

section Eigen

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

theorem exists_mem_eigen_of_prod_eq_zero [Nontrivial M] (C : Module.End K M) (s : Finset K) :
    (∀ v : M, aeval C (∏ z ∈ s, (X - Polynomial.C z)) v = 0) →
      ∃ z ∈ s, ∃ v : M, v ≠ 0 ∧ C v = z • v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact absurd (by simpa using h v) hv
  | insert a s ha ih =>
    intro h
    by_cases hs : ∀ v : M, aeval C (∏ z ∈ s, (X - Polynomial.C z)) v = 0
    · obtain ⟨z, hz, hv⟩ := ih hs
      exact ⟨z, Finset.mem_insert_of_mem hz, hv⟩
    · obtain ⟨u, hu⟩ := not_forall.mp hs
      refine ⟨a, Finset.mem_insert_self a s, aeval C (∏ z ∈ s, (X - Polynomial.C z)) u, hu, ?_⟩
      have h1 := h u
      rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply] at h1
      simpa [sub_eq_zero] using h1

theorem exists_eigenvector_of_pow_eq_one [Nontrivial M] {N : ℕ} (hN : 0 < N) {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) (C : Module.End K M) (hC : C ^ N = 1) :
    ∃ (l : K) (v : M), l ^ N = 1 ∧ v ≠ 0 ∧ C v = l • v := by
  have h0 : ∀ v : M, aeval C (∏ z ∈ nthRootsFinset N (1 : K), (X - Polynomial.C z)) v = 0 := by
    intro v
    rw [← X_pow_sub_one_eq_prod hN hζ]
    simp [hC]
  obtain ⟨z, hz, v, hv0, hv⟩ := exists_mem_eigen_of_prod_eq_zero C _ h0
  exact ⟨z, v, (mem_nthRootsFinset hN 1).1 hz, hv0, hv⟩

theorem pow_apply_eigen {C : Module.End K M} {l : K} {v : M} (hv : C v = l • v) (n : ℕ) :
    (C ^ n) v = l ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ']

theorem orderOf_eq_two_pow_succ (hk : (2 : K) ≠ 0) {l : K} {t : ℕ} (h : l ^ 2 ^ t = -1) :
    orderOf l = 2 ^ (t + 1) := by
  have hne : ¬ l ^ 2 ^ t = 1 := by
    rw [h]
    intro h1
    apply hk
    linear_combination -h1
  have h2 : l ^ 2 ^ (t + 1) = 1 := by
    rw [pow_succ, pow_mul, h]
    norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow hne h2

end Eigen

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
