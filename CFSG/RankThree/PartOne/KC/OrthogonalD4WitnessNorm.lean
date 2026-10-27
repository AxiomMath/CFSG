module

public import CFSG.LocalAnalysis.ComponentInitial.QuadraticLowDimension
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalD4

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section FiniteField

variable {K : Type} [Field K] [Finite K]

theorem two_ne_zero_of_odd_card (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  have := Fintype.ofFinite K
  refine Ring.two_ne_zero fun h => ?_
  have h1 : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two h
  rw [← Nat.card_eq_fintype_card] at h1
  have h3 := Nat.odd_iff.mp hodd
  omega

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_map_eq_one (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K V) : ∃ u : V, Q u = 1 := by
  obtain ⟨e, he0, he⟩ := (finite_odd_quadratic_low_Witt_dimension_bound hodd Q hQ).1 h3
  obtain ⟨f, hf, hef⟩ := quadratic_hyperbolic_partner Q hQ he he0
  refine ⟨e + f, ?_⟩
  rw [QuadraticMap.map_add Q e f, he, hf, hef]
  ring

theorem exists_map_eq_one_orthogonal (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ finrank K V) :
    ∃ u v : V, Q u = 1 ∧ Q v = 1 ∧ polar Q u v = 0 := by
  obtain ⟨u, hu⟩ := exists_map_eq_one hodd Q hQ (by omega)
  have hrefl : (polarBilin Q).IsRefl := (QuadraticMap.isSymm_polarBilin Q).isRefl
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hu
    exact zero_ne_one hu
  have hB2 : (polarBilin Q) u u ≠ 0 := by
    rw [polarBilin_apply_apply, polar_self_eq_two_mul, hu, mul_one]
    exact two_ne_zero_of_odd_card hodd
  have hnd : (LinearMap.BilinForm.restrict (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}))).Nondegenerate :=
    LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton _ hQ hrefl hB2
  have hdim : finrank K (LinearMap.BilinForm.orthogonal (polarBilin Q)
      (Submodule.span K {u})) = finrank K V - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hu0]
  set U := LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) with hU
  have hndQ : (polarBilin (Q.comp U.subtype)).Nondegenerate := by
    have : polarBilin (Q.comp U.subtype) = LinearMap.BilinForm.restrict (polarBilin Q) U := by
      refine LinearMap.ext₂ fun x y => ?_
      simp [polarBilin_apply_apply, polar]
    rw [this]
    exact hnd
  obtain ⟨v, hv⟩ := exists_map_eq_one hodd (Q.comp U.subtype) hndQ (by omega)
  refine ⟨u, (v : V), hu, hv, ?_⟩
  have hv' : (v : V) ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) :=
    v.2
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv'
  have := hv' u (Submodule.mem_span_singleton_self u)
  have h0 : polarBilin Q u (v : V) = 0 := this
  rwa [polarBilin_apply_apply] at h0

end FiniteField

section Reflections

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem map_sub_of_map_eq_one (Q : QuadraticForm K V) {r s : V} (hr : Q r = 1) (hs : Q s = 1) :
    Q (r - s) = 2 - polar Q r s := by
  have h := QuadraticMap.map_add Q r (-s)
  rw [QuadraticMap.map_neg, polar_neg_right, hr, hs] at h
  rw [sub_eq_add_neg, h]
  ring

theorem map_add_of_map_eq_one (Q : QuadraticForm K V) {r s : V} (hr : Q r = 1) (hs : Q s = 1) :
    Q (r + s) = 2 + polar Q r s := by
  rw [QuadraticMap.map_add Q r s, hr, hs]
  ring

theorem exists_isometry_apply_eq (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K V) {r s : V}
    (hr : Q r = 1) (hs : Q s = 1) :
    ∃ k : V ≃ₗ[K] V, k ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ k r = s ∧
      ∀ z, polar Q r z = 0 → polar Q s z = 0 → k z = z := by
  have hsr : polar Q s r = polar Q r s := polar_comm Q s r
  have hrr : polar Q r r = 2 := by rw [polar_self_eq_two_mul, hr, mul_one]
  have hss : polar Q s s = 2 := by rw [polar_self_eq_two_mul, hs, mul_one]
  by_cases hd : Q (r - s) = 0
  · have hB : polar Q r s = 2 := by
      have := map_sub_of_map_eq_one Q hr hs
      rw [hd] at this
      exact (sub_eq_zero.mp this.symm).symm
    have hsum : Q (r + s) = 4 := by
      rw [map_add_of_map_eq_one Q hr hs, hB]
      norm_num
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    have hs0 : Q s ≠ 0 := by rw [hs]; exact one_ne_zero
    have hsum0 : Q (r + s) ≠ 0 := by rw [hsum]; exact h4
    have h1 : reflect Q (r + s) r = -s := by
      rw [reflect_apply hsum0, polar_add_left, hrr, hsr, hB, hsum]
      have : ((2 : K) + 2) / 4 = 1 := by
        rw [div_eq_one_iff_eq h4]
        norm_num
      rw [this, one_smul]
      abel
    refine ⟨reflect Q s * reflect Q (r + s), mul_mem (reflect_mem_orthogonalGroup Q s)
      (reflect_mem_orthogonalGroup Q (r + s)), ?_, fun z hz1 hz2 => ?_⟩
    · rw [LinearEquiv.mul_apply, h1, map_neg, reflect_apply_self hs0, neg_neg]
    · have hz : polar Q (r + s) z = 0 := by rw [polar_add_left, hz1, hz2, add_zero]
      rw [LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero hz,
        reflect_apply_of_polar_eq_zero hz2]
  · refine ⟨reflect Q (r - s), reflect_mem_orthogonalGroup Q _, ?_, fun z hz1 hz2 => ?_⟩
    · have hp : polar Q (r - s) r = Q (r - s) := by
        rw [polar_sub_left, hrr, hsr, map_sub_of_map_eq_one Q hr hs]
      rw [reflect_apply hd, hp, div_self hd, one_smul]
      abel
    · have hz : polar Q (r - s) z = 0 := by rw [polar_sub_left, hz1, hz2, sub_zero]
      exact reflect_apply_of_polar_eq_zero hz

theorem exists_isometry_pair (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K V) {u v u₀ v₀ : V}
    (hu : Q u = 1) (hv : Q v = 1) (huv : polar Q u v = 0) (hu₀ : Q u₀ = 1) (hv₀ : Q v₀ = 1)
    (huv₀ : polar Q u₀ v₀ = 0) :
    ∃ k : V ≃ₗ[K] V, k ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ k u = u₀ ∧ k v = v₀ := by
  obtain ⟨k₁, hk₁, hk₁u, -⟩ := exists_isometry_apply_eq h2 Q hu hu₀
  have hr : Q (k₁ v) = 1 := by rw [map_of_mem hk₁, hv]
  have hr0 : polar Q (k₁ v) u₀ = 0 := by
    rw [← hk₁u, polar_map_of_mem hk₁, polar_comm, huv]
  obtain ⟨k₂, hk₂, hk₂r, hk₂fix⟩ := exists_isometry_apply_eq h2 Q hr hv₀
  refine ⟨k₂ * k₁, mul_mem hk₂ hk₁, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hk₁u]
    exact hk₂fix u₀ hr0 (by rw [polar_comm, huv₀])
  · rw [LinearEquiv.mul_apply, hk₂r]

theorem reflect_mul_reflect_mem_orthDerived (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K V) {u v : V}
    (hu : Q u = 1) (hv : Q v = 1) (huv : polar Q u v = 0) :
    reflect Q u * reflect Q v ∈ orthDerived Q := by
  have hh := reflect_mem_orthogonalGroup Q (u - v)
  have hsu := reflect_mem_orthogonalGroup Q u
  have hhu : reflect Q (u - v) u = v := (reflect_sub_apply h2 hu hv huv).1
  have hc : ⁅reflect Q u, reflect Q (u - v)⁆ = reflect Q u * reflect Q v := by
    have h1 := reflect_conj hh u
    rw [hhu] at h1
    rw [commutatorElement_def, reflect_inv, mul_assoc, mul_assoc, ← mul_assoc (reflect Q (u - v)),
      ← h1]
  rw [← hc]
  exact Subgroup.commutator_mem_commutator hsu hh

end Reflections

end CFSG.RankThree.PartOne.KCOrthogonalD4
