module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

public section

namespace CFSG.RankThree.Lattice

open Polynomial Module

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem charpoly_eq_restrict_mul_mapQ (W : Submodule K V) (e : V →ₗ[K] V)
    (he : W ≤ W.comap e) :
    e.charpoly = (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by
  classical
  let bW := Module.Free.chooseBasis K W
  let bQ := Module.Free.chooseBasis K (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix (Module.Free.ChooseBasisIndex K W) (Module.Free.ChooseBasisIndex K (V ⧸ W)) K :=
    Matrix.of fun i l => (b.repr (e (b (Sum.inr l)))) (Sum.inl i)
  let D := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  have h : LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D := by
    ext u v
    cases u with
    | inl i =>
      cases v with
      | inl k =>
        simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
          LinearMap.toMatrix_apply]
        apply Module.Basis.sumQuot_repr_inl_of_mem
      | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr j =>
      cases v with
      | inl k =>
        suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact he (Submodule.coe_mem (bW k))
      | inr l =>
        simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
          Matrix.fromBlocks_apply₂₂, b, D]
        rw [← Module.Basis.sumQuot_inr bW bQ l, W.mapQ_apply]
        simp
  rw [← LinearMap.charpoly_toMatrix e b, h, Matrix.charpoly_fromBlocks_zero₂₁,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

end Field

section Ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem aeval_restrict_apply (U : Submodule R M) (e : M →ₗ[R] M) (he : ∀ x ∈ U, e x ∈ U)
    (p : R[X]) (u : U) : ((aeval (e.restrict he) p) u : M) = aeval e p (u : M) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial j a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul]
    rw [Module.End.pow_restrict j he, LinearMap.coe_restrict_apply]

@[expose] def cycSpan (e : M →ₗ[R] M) (x : M) : Submodule R M :=
  Submodule.span R (Set.range fun j : ℕ => (e ^ j) x)

theorem pow_apply_mem_cycSpan (e : M →ₗ[R] M) (x : M) (j : ℕ) : (e ^ j) x ∈ cycSpan e x :=
  Submodule.subset_span ⟨j, rfl⟩

theorem cycSpan_le_comap (e : M →ₗ[R] M) (x : M) : cycSpan e x ≤ (cycSpan e x).comap e := by
  rw [cycSpan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, ← Module.End.mul_apply, ← pow_succ']
  exact Submodule.subset_span ⟨j + 1, rfl⟩

theorem aeval_apply_eq_sum (e : M →ₗ[R] M) (x : M) {q : R[X]} {m : ℕ} (hq : q.natDegree < m) :
    aeval e q x = ∑ i : Fin m, q.coeff i • (e ^ (i : ℕ)) x := by
  rw [aeval_eq_sum_range' hq, LinearMap.sum_apply, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem cycSpan_eq_span_of_monic (e : M →ₗ[R] M) (x : M) {p : R[X]} (hp : p.Monic) {k : ℕ}
    (hk : p.natDegree = k) (h : aeval e p x = 0) :
    cycSpan e x = Submodule.span R (Set.range fun j : Fin k => (e ^ (j : ℕ)) x) := by
  set S := Submodule.span R (Set.range fun j : Fin k => (e ^ (j : ℕ)) x) with hS
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨j, rfl⟩
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hj : j < k
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      · push Not at hj
        have hrel : (e ^ k) x = -∑ i ∈ Finset.range k, p.coeff i • (e ^ i) x := by
          have h1 := h
          rw [hp.as_sum, hk, map_add, map_sum] at h1
          simp only [map_pow, aeval_X, aeval_C, map_mul, LinearMap.add_apply,
            LinearMap.sum_apply, Module.End.mul_apply, Module.algebraMap_end_apply] at h1
          exact eq_neg_of_add_eq_zero_left h1
        have hj' : j = (j - k) + k := by omega
        have hwj : (e ^ j) x = -∑ i ∈ Finset.range k, p.coeff i • (e ^ (j - k + i)) x := by
          rw [hj', pow_add, Module.End.mul_apply, hrel, map_neg, map_sum, ← hj']
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, ← Module.End.mul_apply, ← pow_add]
        change (e ^ j) x ∈ S
        rw [hwj]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
        have hi' : i < k := Finset.mem_range.1 hi
        exact ih _ (by omega)
  · rintro _ ⟨j, rfl⟩
    exact ⟨j, rfl⟩

end Ring

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem charpoly_restrict_cycSpan (e : V →ₗ[K] V) (x : V) {p : K[X]} (hp : p.Monic) {k : ℕ}
    (hk : p.natDegree = k) (h : aeval e p x = 0)
    (hli : LinearIndependent K fun j : Fin k => (e ^ (j : ℕ)) x)
    (he : ∀ u ∈ cycSpan e x, e u ∈ cycSpan e x) :
    (e.restrict he).charpoly = p := by
  set g := e.restrict he
  have hfin : finrank K (cycSpan e x) = k := by
    rw [cycSpan_eq_span_of_monic e x hp hk h, finrank_span_eq_card hli, Fintype.card_fin]
  have hcp : g.charpoly.natDegree = k := by rw [LinearMap.charpoly_natDegree, hfin]
  set q := g.charpoly - p with hq
  have hqx : aeval e q x = 0 := by
    have h0 : ((aeval g q) ⟨x, pow_apply_mem_cycSpan e x 0⟩ : V) = 0 := by
      rw [hq, map_sub, LinearMap.aeval_self_charpoly, zero_sub, LinearMap.neg_apply,
        Submodule.coe_neg, aeval_restrict_apply, h, neg_zero]
    rwa [aeval_restrict_apply] at h0
  by_cases hq0 : q = 0
  · exact sub_eq_zero.1 hq0
  have hlt : q.natDegree < k := by
    have hlt : q.degree < g.charpoly.degree := by
      apply Polynomial.degree_sub_lt_left
      · rw [Polynomial.degree_eq_natDegree g.charpoly_monic.ne_zero,
          Polynomial.degree_eq_natDegree hp.ne_zero, hcp, hk]
      · exact g.charpoly_monic.ne_zero
      · rw [g.charpoly_monic.leadingCoeff, hp.leadingCoeff]
    rw [Polynomial.degree_eq_natDegree g.charpoly_monic.ne_zero, hcp] at hlt
    exact (Polynomial.natDegree_lt_iff_degree_lt hq0).2 hlt
  rw [aeval_apply_eq_sum e x hlt] at hqx
  have hc := Fintype.linearIndependent_iff.1 hli _ hqx
  refine absurd ?_ hq0
  ext i
  by_cases hi : i < k
  · exact hc ⟨i, hi⟩
  · rw [Polynomial.coeff_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end Field

end CFSG.RankThree.Lattice
