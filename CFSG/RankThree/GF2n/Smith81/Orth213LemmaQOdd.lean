module

public import Mathlib.FieldTheory.Separable
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.GF2n.Smith81.Orth213.LemmaQ

open Polynomial

theorem two_eq_zero_alg (K : Type*) {A : Type*} [Field K] [CharP K 2] [Ring A] [Algebra K A] :
    (2 : A) = 0 := by
  have : (2 : A) = algebraMap K A 2 := (map_ofNat (algebraMap K A) 2).symm
  rw [this, CharTwo.two_eq_zero, map_zero]

theorem add_self_eq_zero_alg (K : Type*) {A : Type*} [Field K] [CharP K 2] [Ring A] [Algebra K A]
    (a : A) : a + a = 0 := by
  rw [← two_mul, two_eq_zero_alg K, zero_mul]

theorem add_self_eq_zero_mod (K : Type*) [Field K] [CharP K 2] {V : Type*} [AddCommGroup V]
    [Module K V] (v : V) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem neg_eq_self_mod (K : Type*) [Field K] [CharP K 2] {V : Type*} [AddCommGroup V]
    [Module K V] (v : V) : -v = v :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero_mod K v)

theorem exists_odd_pow_eq_one_of_aeval {K A : Type*} [Field K] [CharP K 2] [Ring A] [Algebra K A]
    (S : A) (p : K[X]) (hp : Squarefree p) (hS : aeval S p = 0) {N : ℕ} (hN : 0 < N)
    (hSN : S ^ N = 1) : ∃ k : ℕ, Odd k ∧ S ^ k = 1 := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ S ^ n = 1 := ⟨N, hN, hSN⟩
  refine ⟨Nat.find hex, ?_, (Nat.find_spec hex).2⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨j, hj⟩ := hodd
  have hpos : 0 < Nat.find hex := (Nat.find_spec hex).1
  have hj0 : 0 < j := by omega
  have hSj : S ^ (Nat.find hex) = 1 := (Nat.find_spec hex).2
  have hsq : (S ^ j + 1) ^ 2 = 0 := by
    have : (S ^ j + 1) ^ 2 = S ^ (j + j) + (S ^ j + S ^ j) + 1 := by
      rw [pow_add]; noncomm_ring
    rw [this, add_self_eq_zero_alg K (S ^ j), add_zero, ← hj, hSj]
    exact add_self_eq_zero_alg K 1
  have h1 : minpoly K S ∣ (X ^ j + 1) ^ 2 := by
    apply minpoly.dvd
    simp [hsq]
  have hmsq : Squarefree (minpoly K S) :=
    Squarefree.squarefree_of_dvd (minpoly.dvd K S hS) hp
  have h2 : minpoly K S ∣ X ^ j + 1 := (hmsq.dvd_pow_iff_dvd two_ne_zero).mp h1
  have h3 : aeval S (X ^ j + 1 : K[X]) = 0 := minpoly.dvd_iff.mp h2
  simp only [map_add, map_pow, aeval_X, map_one] at h3
  have h4 : S ^ j = 1 := by
    have h5 : S ^ j = -1 := eq_neg_of_add_eq_zero_left h3
    rw [h5]
    exact neg_eq_of_add_eq_zero_right (add_self_eq_zero_alg K (1 : A))
  exact Nat.find_min hex (m := j) (by omega) ⟨hj0, h4⟩

theorem derivative_cubic (K : Type*) [Field K] [CharP K 2] (t : K) :
    derivative ((X + 1) * (X ^ 2 + C t * X + 1) : K[X]) = X ^ 2 + C (t + 1) := by
  have h2 : (2 : K[X]) = 0 := CharTwo.two_eq_zero
  simp only [derivative_mul, derivative_add, derivative_X, derivative_one, derivative_pow,
    derivative_C, derivative_X_pow, map_add, map_one]
  have h2' : (C ((2 : ℕ) : K) : K[X]) = 0 := by
    rw [Nat.cast_ofNat, CharTwo.two_eq_zero, C_0]
  simp only [h2', zero_mul, zero_add, add_zero, mul_one, Nat.reduceSub, pow_one, one_mul]
  linear_combination (C t * X) * h2

theorem squarefree_cubic (K : Type*) [Field K] [CharP K 2] {t : K} (ht : t ≠ 0) :
    Squarefree ((X + 1) * (X ^ 2 + C t * X + 1) : K[X]) := by
  apply Polynomial.Separable.squarefree
  rw [Polynomial.separable_def']
  have h2 : (2 : K[X]) = 0 := CharTwo.two_eq_zero
  refine ⟨C (t ^ 2)⁻¹, -(C (t ^ 2)⁻¹ * (X + C (t + 1))), ?_⟩
  rw [derivative_cubic]
  have key : C (t ^ 2)⁻¹ * C (t ^ 2) = (1 : K[X]) := by
    rw [← C_mul, inv_mul_cancel₀ (pow_ne_zero 2 ht), C_1]
  simp only [map_add, map_one, map_pow] at key ⊢
  linear_combination (-1 : K[X]) * key - (C (t ^ 2)⁻¹ * C t + 1) * h2

theorem exists_odd_pow_eq_one_of_cubic (K : Type*) [Field K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] [Finite V] (S : V ≃ₗ[K] V) {t : K} (ht : t ≠ 0)
    (h : ∀ v, S (S (S v + v)) + t • S (S v + v) + (S v + v) = 0) :
    ∃ k : ℕ, Odd k ∧ S ^ k = 1 := by
  classical
  have hfin : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  let φ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)
  have hφ : ∀ e : V ≃ₗ[K] V, ∀ v, φ e v = e v := fun e v => rfl
  have hS : aeval (φ S) ((X ^ 2 + C t * X + 1) * (X + 1) : K[X]) = 0 := by
    ext v
    simp only [map_mul, map_add, map_pow, aeval_X, aeval_C, map_one, Module.End.mul_apply,
      LinearMap.add_apply, LinearMap.zero_apply, Module.End.one_apply, pow_two,
      Module.algebraMap_end_apply, hφ]
    have hv := h v
    simp only [map_add, smul_add] at hv
    rw [← hv]
    abel
  obtain ⟨k, hk, hSk⟩ := exists_odd_pow_eq_one_of_aeval (K := K) (φ S) _
    (by rw [mul_comm]; exact squarefree_cubic K ht) hS (N := orderOf S) (orderOf_pos S)
    (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  refine ⟨k, hk, ?_⟩
  have h1 : φ (S ^ k) = φ 1 := by rw [map_pow, hSk, map_one]
  exact LinearEquiv.toLinearMap_injective h1

end CFSG.RankThree.GF2n.Smith81.Orth213.LemmaQ
