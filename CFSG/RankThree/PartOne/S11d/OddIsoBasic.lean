module

public import Mathlib.LinearAlgebra.Semisimple

public section

namespace CFSG.RankThree.PartOne.OddIso

open Polynomial Module

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem natCast_odd_eq_one [CharP K 2] {p : ℕ} (hp : Odd p) : (p : K) = 1 := by
  obtain ⟨m, rfl⟩ := hp
  push_cast
  rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2]
  ring

@[expose] def avg (A : Module.End K V) (p : ℕ) : Module.End K V :=
  ∑ i ∈ Finset.range p, A ^ i

variable {A : Module.End K V} {p : ℕ}

theorem mul_avg (hA : A ^ p = 1) : A * avg A p = avg A p := by
  unfold avg
  rw [Finset.mul_sum]
  have h1 : ∑ i ∈ Finset.range p, A * A ^ i = ∑ i ∈ Finset.range p, A ^ (i + 1) :=
    Finset.sum_congr rfl fun i _ => (pow_succ' A i).symm
  rw [h1]
  have h2 := Finset.sum_range_succ (fun i => A ^ i) p
  have h3 := Finset.sum_range_succ' (fun i => A ^ i) p
  rw [hA] at h2
  rw [pow_zero] at h3
  have h4 : ∑ i ∈ Finset.range p, A ^ (i + 1) + 1 = ∑ i ∈ Finset.range p, A ^ i + 1 := by
    rw [← h3, h2]
  exact add_right_cancel h4

theorem pow_mul_avg (hA : A ^ p = 1) (i : ℕ) : A ^ i * avg A p = avg A p := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, mul_assoc, mul_avg hA, ih]

theorem avg_commute (A : Module.End K V) (p : ℕ) : Commute A (avg A p) := by
  unfold avg
  exact Commute.sum_right _ _ _ fun i _ => (Commute.refl A).pow_right i

theorem avg_mul (hA : A ^ p = 1) : avg A p * A = avg A p := by
  rw [← (avg_commute A p).eq, mul_avg hA]

theorem avg_mul_self [CharP K 2] (hp : Odd p) (hA : A ^ p = 1) :
    avg A p * avg A p = avg A p := by
  have h1 : avg A p * avg A p = ∑ i ∈ Finset.range p, avg A p := by
    conv_lhs => unfold avg
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => pow_mul_avg hA i
  rw [h1, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul K,
    natCast_odd_eq_one hp, one_smul]

theorem sub_one_mul_avg (hA : A ^ p = 1) : (A - 1) * avg A p = 0 := by
  rw [sub_mul, mul_avg hA, one_mul, sub_self]

theorem avg_sub_one_eq [CharP K 2] (hp : Odd p) :
    avg A p - 1 = (A - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, A ^ j := by
  rw [Finset.mul_sum]
  have h1 : ∀ i ∈ Finset.range p, (A - 1) * ∑ j ∈ Finset.range i, A ^ j = A ^ i - 1 :=
    fun i _ => mul_geom_sum A i
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
  unfold avg
  congr 1
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul K, natCast_odd_eq_one hp,
    one_smul]

theorem range_avg [CharP K 2] (hp : Odd p) (hA : A ^ p = 1) :
    LinearMap.range (avg A p) = LinearMap.ker (A - 1) := by
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨u, rfl⟩
    have := congrArg (fun f : Module.End K V => f u) (sub_one_mul_avg hA)
    simpa using this
  · intro hv
    have hv' : A v = v := sub_eq_zero.mp hv
    have hpow : ∀ i : ℕ, (A ^ i) v = v := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', Module.End.mul_apply, ih, hv']
    refine ⟨v, ?_⟩
    unfold avg
    rw [LinearMap.sum_apply]
    simp_rw [hpow]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul K, natCast_odd_eq_one hp,
      one_smul]

theorem ker_avg [CharP K 2] (hp : Odd p) (hA : A ^ p = 1) :
    LinearMap.ker (avg A p) = LinearMap.range (A - 1) := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hv
    refine ⟨-((∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, A ^ j) v), ?_⟩
    have h1 := congrArg (fun f : Module.End K V => f v) (avg_sub_one_eq (A := A) hp)
    simp only [LinearMap.sub_apply, hv, Module.End.one_apply, Module.End.mul_apply] at h1
    rw [map_neg, LinearMap.sub_apply, Module.End.one_apply, ← h1]
    simp
  · rintro ⟨u, rfl⟩
    rw [LinearMap.sub_apply, map_sub, Module.End.one_apply, ← Module.End.mul_apply, avg_mul hA,
      sub_self]

theorem isCompl_ker_range [CharP K 2] (hp : Odd p) (hA : A ^ p = 1) :
    IsCompl (LinearMap.ker (A - 1)) (LinearMap.range (A - 1)) := by
  have h : IsIdempotentElem (avg A p) := avg_mul_self hp hA
  rw [← range_avg hp hA, ← ker_avg hp hA]
  exact LinearMap.IsIdempotentElem.isCompl h

theorem isSemisimple [CharP K 2] (hp : Odd p) (hA : A ^ p = 1) : A.IsSemisimple := by
  have hpK : (p : K) ≠ 0 := by rw [natCast_odd_eq_one hp]; exact one_ne_zero
  have hsq : Squarefree (X ^ p - 1 : K[X]) := by
    have := Polynomial.separable_X_pow_sub_C (1 : K) hpK one_ne_zero
    rw [map_one] at this
    exact this.squarefree
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
  simp [hA]

section Form

variable {σ : K →+* K} (B : V →ₛₗ[σ] V →ₗ[K] K)

theorem B_fix_range (hAB : ∀ v w, B (A v) (A w) = B v w) {v : V} (hv : A v = v) (u : V) :
    B v ((A - 1) u) = 0 := by
  rw [LinearMap.sub_apply, map_sub, Module.End.one_apply]
  have := hAB v u
  rw [hv] at this
  rw [this, sub_self]

theorem B_range_fix (hAB : ∀ v w, B (A v) (A w) = B v w) {v : V} (hv : A v = v) (u : V) :
    B ((A - 1) u) v = 0 := by
  rw [LinearMap.sub_apply, map_sub, LinearMap.sub_apply, Module.End.one_apply]
  have := hAB u v
  rw [hv] at this
  rw [this, sub_self]

end Form

end CFSG.RankThree.PartOne.OddIso
