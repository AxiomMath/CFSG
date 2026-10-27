module

public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

public section

open Module

namespace CFSG.StandardType.QTwoLin

@[expose] def IsTransvectionLin {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) : Prop :=
  ∃ (u : V) (ψ : Dual K V), u ≠ 0 ∧ ψ ≠ 0 ∧ ψ u = 0 ∧ ∀ v, g v = v + ψ v • u

@[expose] def TransvectionFree {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (A : Subgroup (V ≃ₗ[K] V)) : Prop :=
  ∀ g ∈ A, ¬ IsTransvectionLin g

theorem two_ne_zero_of_charP_three {K : Type*} [Field K] [CharP K 3] : (2 : K) ≠ 0 := by
  intro h2
  have h3 : ((3 : ℕ) : K) = 0 := CharP.cast_eq_zero K 3
  push_cast at h3
  exact one_ne_zero (by linear_combination h3 - h2 : (1 : K) = 0)

theorem transvection_of_same_centre {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 3] {c : V} {φ φ' : Dual K V}
    (h : φ c = 2) (h' : φ' c = 2) (hne : φ ≠ φ') :
    IsTransvectionLin (reflection h' * reflection h) := by
  refine ⟨c, φ - φ', ?_, sub_ne_zero.mpr hne, by simp [h, h'], fun v => ?_⟩
  · rintro rfl
    exact two_ne_zero_of_charP_three (K := K) (by simpa using h.symm)
  · rw [LinearEquiv.mul_apply, reflection_apply, reflection_apply]
    simp only [map_sub, map_smul, h', smul_eq_mul, LinearMap.sub_apply]
    module

theorem transvection_of_pair {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 3] {c h : V} {φ α : Dual K V}
    (hφ : φ c = 2) (hα : α h = 2) (ha : φ h = 0) (hb : α c ≠ 0) :
    IsTransvectionLin ((reflection hφ * reflection hα) ^ 2) := by
  have h2 := two_ne_zero_of_charP_three (K := K)
  refine ⟨h, α c • φ, ?_, ?_, by simp [ha], fun v => ?_⟩
  · rintro rfl; exact h2 (by simpa using hα.symm)
  · intro h0
    have := congrArg (fun f : Dual K V => f c) h0
    simp only [LinearMap.smul_apply, hφ, smul_eq_mul, LinearMap.zero_apply] at this
    exact mul_ne_zero hb h2 this
  · rw [pow_two, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      reflection_apply, reflection_apply, reflection_apply, reflection_apply]
    simp only [map_sub, map_smul, hφ, hα, ha, smul_eq_mul, LinearMap.smul_apply]
    module

theorem reflection_dual_eq_of_transvectionFree {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [CharP K 3] {A : Subgroup (V ≃ₗ[K] V)}
    (hTF : TransvectionFree A) {c : V} {φ ψ : Dual K V}
    (hφ : φ c = 2) (hψ : ψ c = 2)
    (hr : reflection hφ ∈ A) (hs : reflection hψ ∈ A) : φ = ψ := by
  by_contra hne
  exact hTF _ (A.mul_mem hs hr) (transvection_of_same_centre hφ hψ hne)

theorem reflection_fixes_of_negated_root {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [CharP K 3] {A : Subgroup (V ≃ₗ[K] V)} (hTF : TransvectionFree A)
    {c x : V} {φ : Dual K V} (hφ : φ c = 2) (hr : reflection hφ ∈ A)
    {z : V ≃ₗ[K] V} (hz : z ∈ A) (hzc : z c = -c) (hzx : z x = x) :
    reflection hφ x = x := by
  have hzic : z.symm c = -c := by
    apply z.injective
    simp [hzc]
  have hzix : z.symm x = x := by
    apply z.injective
    simp [hzx]
  let ψ : Dual K V := -(φ.comp z.symm.toLinearMap)
  have hψ : ψ c = 2 := by
    simp [ψ, hzic, hφ]
  have hconj : reflection hψ = z * reflection hφ * z⁻¹ := by
    ext v
    change v - ψ v • c = z (z.symm v - φ (z.symm v) • c)
    rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, hzc]
    simp only [ψ, LinearMap.neg_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    module
  have hψmem : reflection hψ ∈ A := by
    rw [hconj]
    exact A.mul_mem (A.mul_mem hz hr) (A.inv_mem hz)
  have heq := reflection_dual_eq_of_transvectionFree hTF hφ hψ hr hψmem
  have heqx := congrArg (fun f : Dual K V => f x) heq
  have hneg : φ x = -φ x := by
    simpa [ψ, hzix] using heqx
  have hzero : φ x = 0 := by
    have hmul : (2 : K) * φ x = 0 := by linear_combination hneg
    exact (mul_eq_zero.mp hmul).resolve_left two_ne_zero_of_charP_three
  simp [reflection_apply, hzero]

theorem transvection_of_same_functional
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [CharP K 3]
    {c d : V} {φ : Module.Dual K V}
    (hc : φ c = 2) (hd : φ d = 2) (hne : c ≠ d) :
    IsTransvectionLin (Module.reflection hd * Module.reflection hc) := by
  refine ⟨d - c, φ, ?_, ?_, ?_, ?_⟩
  · intro h0
    exact hne (sub_eq_zero.mp h0).symm
  · intro hφ
    have h2 : (2 : K) = 0 := by simpa [hφ] using hc.symm
    exact two_ne_zero_of_charP_three h2
  · rw [map_sub, hd, hc, sub_self]
  · intro v
    rw [LinearEquiv.mul_apply, Module.reflection_apply, Module.reflection_apply]
    simp only [map_sub, map_smul, hc, smul_eq_mul]
    module

theorem reflection_root_eq_of_transvectionFree
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [CharP K 3]
    {A : Subgroup (V ≃ₗ[K] V)} (hTF : TransvectionFree A)
    {c d : V} {φ : Module.Dual K V}
    (hc : φ c = 2) (hd : φ d = 2)
    (hrc : Module.reflection hc ∈ A) (hrd : Module.reflection hd ∈ A) :
    c = d := by
  by_contra hne
  exact hTF _ (A.mul_mem hrd hrc) (transvection_of_same_functional hc hd hne)

theorem reflection_root_neg_of_dual_neg {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [CharP K 3] {A : Subgroup (V ≃ₗ[K] V)} (hTF : TransvectionFree A)
    {c : V} {φ : Dual K V} (hφ : φ c = 2) (hr : reflection hφ ∈ A)
    {z : V ≃ₗ[K] V} (hz : z ∈ A) (hφz : ∀ v, φ (z v) = -φ v) :
    z c = -c := by
  have hd : φ (-z c) = 2 := by rw [map_neg, hφz c, neg_neg, hφ]
  have hφzi : ∀ v, φ (z.symm v) = -φ v := by
    intro v
    have h := hφz (z.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  have hconj : reflection hd = z * reflection hφ * z⁻¹ := by
    ext v
    change v - φ v • (-z c) = z (z.symm v - φ (z.symm v) • c)
    rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, hφzi v]
    module
  have hrd : reflection hd ∈ A := by
    rw [hconj]
    exact A.mul_mem (A.mul_mem hz hr) (A.inv_mem hz)
  have heq := reflection_root_eq_of_transvectionFree hTF hφ hd hr hrd
  have := congrArg Neg.neg heq
  simpa only [neg_neg] using this.symm

theorem mem_of_negated_of_isCompl {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [CharP K 3] {S : Submodule K V} {x v : V}
    (hcomp : IsCompl S (Submodule.span K ({x} : Set V))) {z : V ≃ₗ[K] V}
    (hS : ∀ s ∈ S, z s = -s) (hx : z x = x) (hv : z v = -v) : v ∈ S := by
  have hmem : v ∈ S ⊔ Submodule.span K ({x} : Set V) := by
    rw [hcomp.sup_eq_top]
    trivial
  obtain ⟨s, hs, y, hy, heq⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have htwo : (2 : K) • (c • x) = 0 := by
    calc
      (2 : K) • (c • x) = z v + v := by
        rw [← heq, map_add, map_smul, hS s hs, hx]
        module
      _ = 0 := by rw [hv]; simp
  have hzero : c • x = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (two_ne_zero_of_charP_three (K := K))
  rw [← heq, hzero, add_zero]
  exact hs

theorem reflection_root_mem_of_axis_fixed {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [CharP K 3] {A : Subgroup (V ≃ₗ[K] V)} (hTF : TransvectionFree A)
    {S : Submodule K V} {x c : V} {φ : Dual K V}
    (hcomp : IsCompl S (Submodule.span K ({x} : Set V)))
    {z : V ≃ₗ[K] V} (hz : z ∈ A) (hS : ∀ s ∈ S, z s = -s) (hx : z x = x)
    (hφ : φ c = 2) (hr : reflection hφ ∈ A) (hφx : φ x = 0) : c ∈ S := by
  apply mem_of_negated_of_isCompl hcomp hS hx
  apply reflection_root_neg_of_dual_neg hTF hφ hr hz
  intro v
  have hmem : v ∈ S ⊔ Submodule.span K ({x} : Set V) := by
    rw [hcomp.sup_eq_top]
    trivial
  obtain ⟨s, hs, y, hy, heq⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [← heq, map_add, map_smul, hS s hs, hx, map_add, map_neg, map_smul, hφx]
  simp [hφx]

theorem reflection_kernel_on_span_of_negated_complement
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [CharP K 3]
    {A : Subgroup (V ≃ₗ[K] V)} (hTF : TransvectionFree A)
    {S : Submodule K V} {x : V} (hcomp : IsCompl S (Submodule.span K ({x} : Set V)))
    {z : V ≃ₗ[K] V} (hz : z ∈ A) (hS : ∀ s ∈ S, z s = -s) (hx : z x = x)
    (h : ι → V) (α : ι → Dual K V) (hα : ∀ i, α i (h i) = 2)
    (hr : ∀ i, reflection (hα i) ∈ A)
    (hker : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span K ({x} : Set V)) :
    ∀ v ∈ Submodule.span K (Set.range h), (∀ i, α i v = 0) → v = 0 := by
  intro v hv hvan
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hker v hvan)
  by_cases hc0 : c = 0
  · simpa [hc0] using hc.symm
  have hax : ∀ i, α i x = 0 := by
    intro i
    have heq := hvan i
    rw [← hc, map_smul, smul_eq_mul] at heq
    exact (mul_eq_zero.mp heq).resolve_left hc0
  have hspan : Submodule.span K (Set.range h) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact reflection_root_mem_of_axis_fixed hTF hcomp hz hS hx (hα i) (hr i) (hax i)
  have hvinf : v ∈ S ⊓ Submodule.span K ({x} : Set V) :=
    ⟨hspan hv, hker v hvan⟩
  rw [hcomp.inf_eq_bot] at hvinf
  exact hvinf

theorem reflection_form_fixed_of_root_stabilizer
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [CharP K 3]
    {H : Subgroup (V ≃ₗ[K] V)} (hTF : TransvectionFree H)
    {c : V} {φ : Module.Dual K V} (hφ : φ c = 2)
    (hr : reflection hφ ∈ H) {g : V ≃ₗ[K] V} (hg : g ∈ H)
    (hgc : g c = c) : ∀ v, φ (g v) = φ v := by
  have hgic : g.symm c = c := by
    apply g.injective
    simp [hgc]
  let ψ : Module.Dual K V := φ.comp g.symm.toLinearMap
  have hψ : ψ c = 2 := by simp [ψ, hgic, hφ]
  have hconj : reflection hψ = g * reflection hφ * g⁻¹ := by
    ext v
    change v - ψ v • c = g (g.symm v - φ (g.symm v) • c)
    rw [map_sub, map_smul, g.apply_symm_apply, hgc]
    rfl
  have hψmem : reflection hψ ∈ H := by
    rw [hconj]
    exact H.mul_mem (H.mul_mem hg hr) (H.inv_mem hg)
  have heq := reflection_dual_eq_of_transvectionFree hTF hφ hψ hr hψmem
  intro v
  have h := congrArg (fun f : Module.Dual K V => f (g v)) heq
  simpa [ψ] using h

end CFSG.StandardType.QTwoLin
