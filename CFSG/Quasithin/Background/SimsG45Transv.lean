module

public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Quasithin.SimsG45

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem bilin_skew (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (x y : V) :
    B x y = - B y x := by
  have h : LinearMap.IsAlt B := halt
  exact (h.neg y x).symm

theorem exists_pair_eq_one (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {u : V} (hu : u ≠ 0) : ∃ v, B v u = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, B u y ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (hnd u h)
  have hy' : B y u ≠ 0 := by
    rw [bilin_skew B halt y u]
    exact neg_ne_zero.mpr hy
  refine ⟨(B y u)⁻¹ • y, ?_⟩
  rw [LinearMap.map_smul₂, smul_eq_mul, inv_mul_cancel₀ hy']

theorem exists_orth_not_orth (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {u w : V} (hu : u ≠ 0) (huw : B u w ≠ 0) :
    ∃ v, B v u = 0 ∧ B v w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, hv₀⟩ := exists_pair_eq_one B halt hnd hu
  have hw : w - B v₀ w • u = 0 := by
    apply hnd
    intro y
    have h1 : B (y - B y u • v₀) u = 0 := by
      rw [LinearMap.map_sub₂, LinearMap.map_smul₂, hv₀, smul_eq_mul, mul_one, sub_self]
    have h2 := hcon _ h1
    rw [LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul] at h2
    rw [bilin_skew B halt _ y, map_sub, map_smul, smul_eq_mul]
    linear_combination -h2
  have h3 : w = B v₀ w • u := sub_eq_zero.mp hw
  apply huw
  have h4 : B u w = B u (B v₀ w • u) := congrArg (B u) h3
  rw [h4, map_smul, smul_eq_mul, halt u, mul_zero]

theorem exists_transv_form (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (g : V ≃ₗ[F] V) (hg : ∀ x y, B (g x) (g y) = B x y)
    (hrank : Module.finrank F (LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)) = 1) :
    ∃ u : V, u ≠ 0 ∧ ∃ c : F, c ≠ 0 ∧ (∀ v, g v = v + (c * B v u) • u) ∧
      LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id) = F ∙ u := by
  set R := LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)
  obtain ⟨u', hu'0, hu'⟩ := finrank_eq_one_iff'.mp hrank
  have hu0 : (u' : V) ≠ 0 := fun h => hu'0 (Subtype.ext h)
  have hRspan : R = F ∙ (u' : V) := by
    ext w
    constructor
    · intro hw
      obtain ⟨c, hc⟩ := hu' ⟨w, hw⟩
      exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
    · intro hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      exact R.smul_mem c u'.2
  have hex : ∀ x, ∃ a : F, a • (u' : V) = g x - x := by
    intro x
    have hx : g x - x ∈ R := ⟨x, by simp⟩
    rw [hRspan] at hx
    exact Submodule.mem_span_singleton.mp hx
  choose a ha using hex
  have key : ∀ x y, a y * B x u' = a x * B y u' := by
    intro x y
    have h1 := hg x y
    have hgx : g x = x + a x • (u' : V) := by rw [ha x]; abel
    have hgy : g y = y + a y • (u' : V) := by rw [ha y]; abel
    rw [hgx, hgy] at h1
    simp only [LinearMap.map_add₂, LinearMap.map_smul₂, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, halt (u' : V)] at h1
    rw [bilin_skew B halt (u' : V) y] at h1
    linear_combination h1
  obtain ⟨v₀, hv₀⟩ := exists_pair_eq_one B halt hnd hu0
  have hform : ∀ w, a w = a v₀ * B w u' := by
    intro w
    have h := key v₀ w
    rwa [hv₀, mul_one] at h
  have hg' : ∀ v, g v = v + (a v₀ * B v u') • (u' : V) := by
    intro v
    rw [← hform v, ha v]
    abel
  have hc : a v₀ ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ : (u' : V) ∈ R := u'.2
    have hgx := hg' x
    rw [h0, zero_mul, zero_smul, add_zero] at hgx
    apply hu0
    rw [← hx]
    simp [hgx]
  exact ⟨u', hu0, a v₀, hc, hg', hRspan⟩

theorem transv_commute_iff (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {u w : V} (hu : u ≠ 0) {c d : F}
    (hc : c ≠ 0) (hd : d ≠ 0) {a b : V ≃ₗ[F] V} (ha : ∀ v, a v = v + (c * B v u) • u)
    (hb : ∀ v, b v = v + (d * B v w) • w) : a * b = b * a ↔ B u w = 0 := by
  have hdiff : ∀ v, (a * b) v - (b * a) v =
      (c * d * (B v w * B w u)) • u - (c * d * (B v u * B u w)) • w := by
    intro v
    simp only [LinearEquiv.mul_apply, ha, hb, LinearMap.map_add₂, LinearMap.map_smul₂,
      smul_eq_mul]
    module
  have hBwu : B w u = - B u w := bilin_skew B halt w u
  constructor
  · intro hab
    by_contra huw
    obtain ⟨v, hv1, hv2⟩ := exists_orth_not_orth B halt hnd hu huw
    have h1 := hdiff v
    simp only [hab, sub_self, hv1, zero_mul, mul_zero, zero_smul, sub_zero] at h1
    rcases smul_eq_zero.mp h1.symm with h | h
    · exact mul_ne_zero (mul_ne_zero hc hd)
        (mul_ne_zero hv2 (by rw [hBwu]; exact neg_ne_zero.mpr huw)) h
    · exact hu h
  · intro huw
    refine LinearEquiv.ext fun v => sub_eq_zero.mp ?_
    simp only [hdiff v, hBwu, huw, neg_zero, mul_zero, zero_smul, sub_zero]

theorem transv_mul_self [CharP F 2] (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    {u : V} {c : F} {a : V ≃ₗ[F] V} (ha : ∀ v, a v = v + (c * B v u) • u) : a * a = 1 := by
  refine LinearEquiv.ext fun v => ?_
  change a (a v) = v
  simp only [ha, LinearMap.map_add₂, LinearMap.map_smul₂, smul_eq_mul, halt u, mul_zero,
    add_zero]
  rw [add_assoc, ← two_smul F ((c * B v u) • u), CharTwo.two_eq_zero, zero_smul, add_zero]

theorem finrank_sup_pair {u w : V} (hind : LinearIndependent F ![u, w]) :
    Module.finrank F ↥((F ∙ u) ⊔ (F ∙ w)) = 2 := by
  have h := finrank_span_eq_card hind
  rw [Matrix.range_cons_cons_empty, Submodule.span_insert] at h
  simpa using h

theorem nondegLine_sup (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    {u w : V} (hu : u ≠ 0) (huw : B u w ≠ 0) :
    Module.finrank F ↥((F ∙ u) ⊔ (F ∙ w)) = 2 ∧
      ∀ x ∈ (F ∙ u) ⊔ (F ∙ w), (∀ y ∈ (F ∙ u) ⊔ (F ∙ w), B x y = 0) → x = 0 := by
  have hwu : B w u ≠ 0 := by
    rw [bilin_skew B halt w u]
    exact neg_ne_zero.mpr huw
  refine ⟨?_, ?_⟩
  · apply finrank_sup_pair
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have h1 := congrArg (B u) hst
      simp only [map_add, map_smul, map_zero, smul_eq_mul, halt u, mul_zero, zero_add] at h1
      exact (mul_eq_zero.mp h1).resolve_right huw
    subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hu, rfl⟩
  · intro x hx hperp
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hy₁
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hy₂
    have hu_mem : u ∈ (F ∙ u) ⊔ (F ∙ w) :=
      Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)
    have hw_mem : w ∈ (F ∙ u) ⊔ (F ∙ w) :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
    have h1 := hperp u hu_mem
    have h2 := hperp w hw_mem
    simp only [LinearMap.map_add₂, LinearMap.map_smul₂, smul_eq_mul, halt u, halt w, mul_zero,
      add_zero, zero_add] at h1 h2
    have hβ : β = 0 := (mul_eq_zero.mp h1).resolve_right hwu
    have hα : α = 0 := (mul_eq_zero.mp h2).resolve_right huw
    rw [hα, hβ, zero_smul, zero_smul, add_zero]

theorem totSingLine_sup (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    {u w : V} (hu : u ≠ 0) (hw : w ≠ 0) (hne : (F ∙ u) ≠ (F ∙ w)) (huw : B u w = 0) :
    Module.finrank F ↥((F ∙ u) ⊔ (F ∙ w)) = 2 ∧
      ∀ x ∈ (F ∙ u) ⊔ (F ∙ w), ∀ y ∈ (F ∙ u) ⊔ (F ∙ w), B x y = 0 := by
  have hwu : B w u = 0 := by rw [bilin_skew B halt w u, huw, neg_zero]
  refine ⟨?_, ?_⟩
  · apply finrank_sup_pair
    rw [LinearIndependent.pair_iff' hu]
    intro a ha
    apply hne
    have hunit : IsUnit a := by
      refine isUnit_iff_ne_zero.mpr ?_
      rintro rfl
      exact hw (by rw [← ha, zero_smul])
    rw [← ha, Submodule.span_singleton_smul_eq hunit]
  · intro x hx y hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hx₁
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hx₂
    obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.mp hy₁
    obtain ⟨δ, rfl⟩ := Submodule.mem_span_singleton.mp hy₂
    simp only [LinearMap.map_add₂, LinearMap.map_smul₂, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, halt u, halt w, huw, hwu, mul_zero, add_zero]

end CFSG.Quasithin.SimsG45
