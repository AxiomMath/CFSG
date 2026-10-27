module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Nakayama

public noncomputable section

namespace CFSG

open MvPolynomial

universe u v w

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A] {σ : Type w}

attribute [local instance] MvPolynomial.gradedAlgebra

@[expose] def eliminationIdeal (S : Set (MvPolynomial σ A)) : Ideal A :=
  Ideal.span {a | ∃ N : ℕ, ∀ d : σ →₀ ℕ, d.degree = N → monomial d a ∈ Ideal.span S}

theorem apply_eq_zero_of_mem_eliminationIdeal {S : Set (MvPolynomial σ A)} (y : A →ₐ[k] k)
    {v : σ → k} (hv : v ≠ 0) (hS : ∀ f ∈ S, eval v (map (y : A →+* k) f) = 0) {a : A}
    (ha : a ∈ eliminationIdeal S) : y a = 0 := by
  have hker : Ideal.span S ≤ RingHom.ker ((eval v).comp (map (y : A →+* k))) :=
    Ideal.span_le.2 fun f hf => hS f hf
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  refine (Ideal.span_le (I := RingHom.ker (y : A →+* k))).2 ?_ ha
  rintro b ⟨N, hN⟩
  have h := hker (hN (Finsupp.single i N) (Finsupp.degree_single i N))
  rw [RingHom.mem_ker, RingHom.comp_apply, map_monomial, eval_monomial,
    Finsupp.prod_single_index (h := fun n e => v n ^ e) (pow_zero (v i))] at h
  rw [SetLike.mem_coe, RingHom.mem_ker]
  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hi)

theorem mem_smul_span_monomial {J : Ideal A} {N : ℕ} {r : MvPolynomial σ A}
    (hr : r.IsHomogeneous N) (hJ : ∀ m, r.coeff m ∈ J) :
    r ∈ J • Submodule.span A ((fun d => monomial d (1 : A)) '' {d | d.degree = N}) := by
  rw [r.as_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdN : d.degree = N := by
    by_contra h
    exact (mem_support_iff.mp hd) (hr.coeff_eq_zero h)
  rw [show monomial d (r.coeff d) = r.coeff d • monomial d (1 : A) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem_smul (hJ d) (Submodule.subset_span ⟨d, hdN, rfl⟩)

theorem finite_setOf_degree_eq [Finite σ] (N : ℕ) : {d : σ →₀ ℕ | d.degree = N}.Finite := by
  classical
  have := Fintype.ofFinite σ
  refine (Finset.univ.finsuppAntidiag N).finite_toSet.subset fun d hd => ?_
  rw [Finset.mem_coe, Finset.mem_finsuppAntidiag]
  exact ⟨by rw [← Finsupp.degree_eq_sum]; exact hd, Finset.subset_univ _⟩

theorem exists_mem_eliminationIdeal_apply_ne_zero [IsAlgClosed k] [Finite σ]
    {S : Set (MvPolynomial σ A)} (hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n) (y : A →ₐ[k] k)
    (h0 : ∀ v : σ → k, (∀ f ∈ S, eval v (map (y : A →+* k) f) = 0) → v = 0) :
    ∃ a ∈ eliminationIdeal S, y a ≠ 0 := by
  classical
  have := Fintype.ofFinite σ
  have hy : Function.Surjective (y : A →+* k) := fun c => ⟨algebraMap k A c, y.commutes c⟩
  have hφ : Function.Surjective (map (σ := σ) (y : A →+* k)) := map_surjective _ hy
  have hX : ∀ i, ∃ e, (X i : MvPolynomial σ k) ^ e ∈
      Ideal.map (map (y : A →+* k)) (Ideal.span S) := by
    intro i
    have hmem : (X i : MvPolynomial σ k) ∈
        vanishingIdeal k (zeroLocus k (Ideal.map (map (y : A →+* k)) (Ideal.span S))) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      have hx0 : x = 0 := h0 x fun f hf => by
        have := (mem_zeroLocus_iff.mp hx) _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hf))
        rwa [← coe_aeval_eq_eval]
      simp [hx0]
    rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
    exact Ideal.mem_radical_iff.mp hmem
  choose e he using hX
  obtain ⟨E, hE⟩ : ∃ E, ∀ i, (X i : MvPolynomial σ k) ^ E ∈
      Ideal.map (map (y : A →+* k)) (Ideal.span S) := by
    refine ⟨∑ i, e i, fun i => ?_⟩
    have hle : e i ≤ ∑ j, e j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
    rw [← Nat.add_sub_of_le hle, pow_add]
    exact Ideal.mul_mem_right _ _ (he i)
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card σ * E + 1 := ⟨_, rfl⟩
  have hmon : ∀ d : σ →₀ ℕ, d.degree = N →
      monomial d (1 : k) ∈ Ideal.map (map (y : A →+* k)) (Ideal.span S) := by
    intro d hd
    obtain ⟨i, hi⟩ : ∃ i, E ≤ d i := by
      by_contra hcon
      push Not at hcon
      have hle : d.degree ≤ Fintype.card σ * E := by
        rw [Finsupp.degree_eq_sum]
        calc ∑ i, d i ≤ ∑ _i : σ, E := Finset.sum_le_sum fun i _ => (hcon i).le
          _ = Fintype.card σ * E := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [hd, hN] at hle
      exact Nat.not_succ_le_self _ hle
    have hsingle : Finsupp.single i E ≤ d := Finsupp.single_le_iff.mpr hi
    rw [show monomial d (1 : k) = X i ^ E * monomial (d - Finsupp.single i E) 1 by
      rw [X_pow_eq_monomial, monomial_mul, one_mul, add_tsub_cancel_of_le hsingle]]
    exact Ideal.mul_mem_right _ _ (hE i)
  set P : Submodule A (MvPolynomial σ A) :=
    Submodule.span A ((fun d => monomial d (1 : A)) '' {d | d.degree = N}) with hP
  have hhom : (Ideal.span S).IsHomogeneous (homogeneousSubmodule σ A) :=
    Ideal.homogeneous_span _ S fun f hf => by
      obtain ⟨n, hn⟩ := hS f hf
      exact ⟨n, (mem_homogeneousSubmodule n f).2 hn⟩
  have hPle : P ≤ (Ideal.span S).restrictScalars A ⊔ RingHom.ker (y : A →+* k) • P := by
    rw [hP, Submodule.span_le]
    rintro _ ⟨d, hd, rfl⟩
    change monomial d (1 : A) ∈ _
    obtain ⟨g, hg, hgd⟩ := (Ideal.mem_map_iff_of_surjective _ hφ).1 (hmon d hd)
    have hker : monomial d (1 : A) - g ∈ Ideal.map C (RingHom.ker (y : A →+* k)) := by
      rw [← ker_map, RingHom.mem_ker, map_sub, hgd, map_monomial, map_one, sub_self]
    have hsplit : monomial d (1 : A) =
        homogeneousComponent N g + homogeneousComponent N (monomial d (1 : A) - g) := by
      rw [map_sub, homogeneousComponent_eq_self (isHomogeneous_monomial _ hd)]
      abel
    rw [hsplit]
    refine Submodule.add_mem_sup ((Submodule.restrictScalars_mem A _ _).2
      (homogeneousComponent_mem_of_mem hhom hg N)) ?_
    refine mem_smul_span_monomial (homogeneousComponent_isHomogeneous N _) fun m => ?_
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact mem_map_C_iff.mp hker m
    · exact Ideal.zero_mem _
  have hPfg : P.FG := Submodule.fg_span ((finite_setOf_degree_eq N).image _)
  obtain ⟨r, hr1, hrP⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hPfg le_rfl hPle
  refine ⟨r, Ideal.subset_span ⟨N, fun d hd => ?_⟩, fun hr => ?_⟩
  · have hmem := hrP (Submodule.smul_mem_pointwise_smul _ r _
      (Submodule.subset_span ⟨d, hd, rfl⟩ : monomial d (1 : A) ∈ P))
    rwa [Submodule.restrictScalars_mem, smul_monomial, smul_eq_mul, mul_one] at hmem
  · rw [RingHom.mem_ker, map_sub, map_one] at hr1
    rw [show (y : A →+* k) r = y r from rfl, hr, zero_sub] at hr1
    exact one_ne_zero (neg_eq_zero.mp hr1)

theorem forall_mem_eliminationIdeal_iff [IsAlgClosed k] [Finite σ] {S : Set (MvPolynomial σ A)}
    (hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n) (y : A →ₐ[k] k) :
    (∀ a ∈ eliminationIdeal S, y a = 0) ↔
      ∃ v : σ → k, v ≠ 0 ∧ ∀ f ∈ S, eval v (map (y : A →+* k) f) = 0 := by
  refine ⟨fun h => ?_, fun ⟨v, hv, hvS⟩ a ha => apply_eq_zero_of_mem_eliminationIdeal y hv hvS ha⟩
  by_contra hne
  push Not at hne
  obtain ⟨a, ha, hya⟩ := exists_mem_eliminationIdeal_apply_ne_zero hS y fun v hv => by
    by_contra hv0
    obtain ⟨f, hf, hfv⟩ := hne v hv0
    exact hfv (hv f hf)
  exact hya (h a ha)

end CFSG
