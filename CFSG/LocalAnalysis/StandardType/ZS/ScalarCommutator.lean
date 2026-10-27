module

public import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl
public import CFSG.LocalAnalysis.StandardType.ZS.ReflProductOrder
import CFSG.LocalAnalysis.StandardType.GGWitSlpmConjAux
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import CFSG.LocalAnalysis.StandardType.GGWitSlpm

public section

namespace CFSG.StandardType.ZS

open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U]

local instance (priority := high) zsc_zmodAddCommGroup : AddCommGroup (ZMod p) :=
  Ring.toAddCommGroup


omit [Module.Finite (ZMod p) U] in
theorem apply_eq_self_of_mem_ker_inf {u u' : U} {φ ψ : Dual (ZMod p) U}
    {t t' : U ≃ₗ[ZMod p] U} (ht : ∀ v, t v = v - φ v • u)
    (ht' : ∀ v, t' v = v - ψ v • u') {v : U}
    (hv : v ∈ LinearMap.ker φ ⊓ LinearMap.ker ψ) : (t' * t) v = v := by
  have hφv : φ v = 0 := LinearMap.mem_ker.mp hv.1
  have hψv : ψ v = 0 := LinearMap.mem_ker.mp hv.2
  rw [LinearEquiv.mul_apply, ht v, hφv, zero_smul, sub_zero, ht' v, hψv, zero_smul, sub_zero]

theorem finrank_ker_inf_ge {u u' : U} {φ ψ : Dual (ZMod p) U} (hφ : φ u = 2)
    (hψ : ψ u' = 2) (h2 : (2 : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) U - 2 ≤
      Module.finrank (ZMod p) ↥(LinearMap.ker φ ⊓ LinearMap.ker ψ) := by
  have h1 : Module.finrank (ZMod p) ↥(LinearMap.ker φ) = Module.finrank (ZMod p) U - 1 :=
    wSlpmC_finrank_ker u φ hφ h2
  have h1' : Module.finrank (ZMod p) ↥(LinearMap.ker ψ) = Module.finrank (ZMod p) U - 1 :=
    wSlpmC_finrank_ker u' ψ hψ h2
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker φ) (LinearMap.ker ψ)
  have hle : Module.finrank (ZMod p) ↥(LinearMap.ker φ ⊔ LinearMap.ker ψ) ≤
      Module.finrank (ZMod p) U := Submodule.finrank_le _
  omega

omit [Module.Finite (ZMod p) U] in
theorem apply_sub_apply_mem_span {u u' : U} {φ ψ : Dual (ZMod p) U}
    {t t' : U ≃ₗ[ZMod p] U} (ht : ∀ v, t v = v - φ v • u)
    (ht' : ∀ v, t' v = v - ψ v • u') (v : U) :
    (t' * t) v - v ∈ Submodule.span (ZMod p) ({u, u'} : Set U) := by
  have hsub : (t' * t) v - v = -((φ v) • u) - (ψ (t v)) • u' := by
    rw [LinearEquiv.mul_apply, ht' (t v), ht v]
    abel
  rw [hsub]
  have hu : u ∈ Submodule.span (ZMod p) ({u, u'} : Set U) :=
    Submodule.subset_span (Set.mem_insert u {u'})
  have hu' : u' ∈ Submodule.span (ZMod p) ({u, u'} : Set U) :=
    Submodule.subset_span (Set.mem_insert_of_mem u rfl)
  exact Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hu))
    (Submodule.smul_mem _ _ hu')

omit [Module.Finite (ZMod p) U] in
theorem mem_span_of_apply_eq_smul {u u' : U} {φ ψ : Dual (ZMod p) U}
    {t t' : U ≃ₗ[ZMod p] U} (ht : ∀ v, t v = v - φ v • u)
    (ht' : ∀ v, t' v = v - ψ v • u') {a : ZMod p} (ha : a ≠ 1) {v : U}
    (hv : (t' * t) v = a • v) : v ∈ Submodule.span (ZMod p) ({u, u'} : Set U) := by
  have hmem := apply_sub_apply_mem_span ht ht' v
  have hlam : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have hdiff : (t' * t) v - v = (a - 1) • v := by
    rw [hv, sub_smul, one_smul]
  have hveq : v = (a - 1)⁻¹ • ((t' * t) v - v) := by
    rw [hdiff, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  rw [hveq]
  exact Submodule.smul_mem _ _ hmem


omit [Module.Finite (ZMod p) U] in
private theorem zsc_zeta_ne_zero {t t' h : U ≃ₗ[ZMod p] U} {u : U} {φ : Dual (ZMod p) U}
    (hφ : φ u = 2) (h2 : (2 : ZMod p) ≠ 0) (ht : ∀ v, t v = v - φ v • u)
    {ζ : ZMod p} (hconj : ∀ v, h (t' (t v)) = ζ • t' (t (h v))) : ζ ≠ 0 := by
  intro h0
  have hu0 : u ≠ 0 := wSlpmC_ne_zero hφ h2
  have hgu : (t' * t) u = 0 := by
    have hv : h ((t' * t) u) = 0 := by
      have hc := hconj u
      rw [h0, zero_smul] at hc
      exact hc
    exact h.map_eq_zero_iff.mp hv
  rw [LinearEquiv.mul_apply, wSlpmC_of_refl_a hφ t ht] at hgu
  have hz : t' u = 0 := by simpa using hgu
  exact hu0 (t'.injective (by rw [hz, map_zero]))

private theorem zsc_zeta_inv_data {ζ : ZMod p} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (hζ2 : ζ ^ 2 ≠ 1) :
    ζ⁻¹ ≠ 1 ∧ ζ⁻¹ * ζ⁻¹ ≠ 1 ∧ ζ⁻¹ * ζ⁻¹ ≠ ζ⁻¹ := by
  have h1 : ζ⁻¹ ≠ 1 := fun h => hζ1 (inv_eq_one.mp h)
  have h2 : ζ⁻¹ * ζ⁻¹ ≠ 1 := by
    intro h
    apply hζ2
    have h' : (ζ ^ 2)⁻¹ = 1 := by
      rw [pow_two, mul_inv_rev]
      exact h
    exact inv_eq_one.mp h'
  have h3 : ζ⁻¹ * ζ⁻¹ ≠ ζ⁻¹ := by
    intro h
    have h4 : ζ⁻¹ = 1 := by
      calc ζ⁻¹ = (ζ⁻¹ * ζ⁻¹) * ζ := by rw [mul_assoc, inv_mul_cancel₀ hζ0, mul_one]
        _ = ζ⁻¹ * ζ := by rw [h]
        _ = 1 := inv_mul_cancel₀ hζ0
    exact hζ1 (inv_eq_one.mp h4)
  exact ⟨h1, h2, h3⟩

omit [Module.Finite (ZMod p) U] in
private theorem zsc_eigenspace_map {t t' h : U ≃ₗ[ZMod p] U} {ζ : ZMod p} (hζ0 : ζ ≠ 0)
    (hconj : ∀ v, h (t' (t v)) = ζ • t' (t (h v))) (a : ZMod p) :
    (Module.End.eigenspace (t' * t : U →ₗ[ZMod p] U) a).map (h : U →ₗ[ZMod p] U) ≤
      Module.End.eigenspace (t' * t : U →ₗ[ZMod p] U) (ζ⁻¹ * a) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  rw [Submodule.mem_comap] at ⊢
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hv' : t' (t v) = a • v := hv
  have hc := hconj v
  rw [hv', map_smul] at hc
  have hG : t' (t (h v)) = (ζ⁻¹ * a) • h v := by
    calc t' (t (h v)) = ζ⁻¹ • (ζ • t' (t (h v))) := by
          rw [smul_smul, inv_mul_cancel₀ hζ0, one_smul]
      _ = ζ⁻¹ • (a • h v) := by rw [← hc]
      _ = (ζ⁻¹ * a) • h v := by rw [mul_smul]
  exact hG

private theorem zsc_eigenspace_finrank_le {t t' h : U ≃ₗ[ZMod p] U} {ζ : ZMod p}
    (hζ0 : ζ ≠ 0) (hconj : ∀ v, h (t' (t v)) = ζ • t' (t (h v))) (a : ZMod p) :
    Module.finrank (ZMod p) (Module.End.eigenspace (t' * t : U →ₗ[ZMod p] U) a) ≤
      Module.finrank (ZMod p) (Module.End.eigenspace (t' * t : U →ₗ[ZMod p] U) (ζ⁻¹ * a)) := by
  calc Module.finrank (ZMod p) (Module.End.eigenspace (t' * t : U →ₗ[ZMod p] U) a)
      = Module.finrank (ZMod p)
          ((Module.End.eigenspace (t' * t : U →ₗ[ZMod p] U) a).map (h : U →ₗ[ZMod p] U)) :=
        (LinearEquiv.finrank_map_eq h _).symm
    _ ≤ Module.finrank (ZMod p)
          (Module.End.eigenspace (t' * t : U →ₗ[ZMod p] U) (ζ⁻¹ * a)) :=
        Submodule.finrank_mono (zsc_eigenspace_map hζ0 hconj a)

omit [Module.Finite (ZMod p) U] in
private theorem zsc_eigenspaces_disjoint {t t' : U ≃ₗ[ZMod p] U} {a b : ZMod p} (hab : a ≠ b) :
    Module.End.eigenspace (t' * t : U →ₗ[ZMod p] U) a ⊓
      Module.End.eigenspace (t' * t : U →ₗ[ZMod p] U) b = ⊥ := by
  refine eq_bot_iff.mpr ?_
  intro v hv
  have hva : (t' * t : Module.End (ZMod p) U) v = a • v :=
    Module.End.mem_eigenspace_iff.mp hv.1
  have hvb : (t' * t : Module.End (ZMod p) U) v = b • v :=
    Module.End.mem_eigenspace_iff.mp hv.2
  have hzero : (a - b) • v = 0 := by rw [sub_smul, ← hva, ← hvb, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hab)


omit [Module.Finite (ZMod p) U] in
private theorem zsc_finrank_span_pair_le_two {u u' : U} (hu : u ≠ 0) (hu' : u' ≠ 0) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) ({u, u'} : Set U)) ≤ 2 := by
  have hSle : Submodule.span (ZMod p) ({u, u'} : Set U) ≤
      Submodule.span (ZMod p) ({u} : Set U) ⊔ Submodule.span (ZMod p) ({u'} : Set U) := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
    · exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hpair : Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) ({u} : Set U) ⊔
        Submodule.span (ZMod p) ({u'} : Set U)) ≤ 2 := by
    have h := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span (ZMod p) ({u} : Set U)) (Submodule.span (ZMod p) ({u'} : Set U))
    rw [finrank_span_singleton hu, finrank_span_singleton hu'] at h
    omega
  calc Module.finrank (ZMod p) (Submodule.span (ZMod p) ({u, u'} : Set U))
      ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({u} : Set U) ⊔
          Submodule.span (ZMod p) ({u'} : Set U)) := Submodule.finrank_mono hSle
    _ ≤ 2 := hpair

theorem finrank_le_three_of_apply_mul_eq_smul (hp : p ≠ 2) {t t' h : U ≃ₗ[ZMod p] U}
    (ht : IsRefl p t) (ht' : IsRefl p t') {ζ : ZMod p} (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1)
    (hconj : ∀ v, h (t' (t v)) = ζ • t' (t (h v))) : Module.finrank (ZMod p) U ≤ 3 := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  obtain ⟨u, φ, hφ, htform⟩ := wSlpmC_isRefl_form h2 t ht
  obtain ⟨u', ψ, hψ, ht'form⟩ := wSlpmC_isRefl_form h2 t' ht'
  have hζ0 : ζ ≠ 0 := zsc_zeta_ne_zero hφ h2 htform hconj
  let G : Module.End (ZMod p) U := (t' * t : U →ₗ[ZMod p] U)
  let E : ZMod p → Submodule (ZMod p) U := fun a => Module.End.eigenspace G a
  let F : Submodule (ZMod p) U := LinearMap.ker φ ⊓ LinearMap.ker ψ
  have hGF : ∀ v ∈ F, G v = v := fun v hv => apply_eq_self_of_mem_ker_inf htform ht'form hv
  have hFdim : Module.finrank (ZMod p) U - 2 ≤ Module.finrank (ZMod p) F :=
    finrank_ker_inf_ge hφ hψ h2
  have hE1 : F ≤ E 1 := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff]
    simpa using hGF v hv
  obtain ⟨hζinv, hζinv2, hζdist⟩ := zsc_zeta_inv_data hζ0 hζ1 hζ2
  have hle : ∀ a, Module.finrank (ZMod p) (E a) ≤
      Module.finrank (ZMod p) (E (ζ⁻¹ * a)) :=
    zsc_eigenspace_finrank_le hζ0 hconj
  have hEa : Module.finrank (ZMod p) U - 2 ≤ Module.finrank (ZMod p) (E ζ⁻¹) := by
    calc Module.finrank (ZMod p) U - 2 ≤ Module.finrank (ZMod p) F := hFdim
      _ ≤ Module.finrank (ZMod p) (E 1) := Submodule.finrank_mono hE1
      _ ≤ Module.finrank (ZMod p) (E (ζ⁻¹ * 1)) := hle 1
      _ = Module.finrank (ZMod p) (E ζ⁻¹) := by rw [mul_one]
  have hEb : Module.finrank (ZMod p) U - 2 ≤
      Module.finrank (ZMod p) (E (ζ⁻¹ * ζ⁻¹)) := by
    calc Module.finrank (ZMod p) U - 2 ≤ Module.finrank (ZMod p) (E ζ⁻¹) := hEa
      _ ≤ Module.finrank (ZMod p) (E (ζ⁻¹ * ζ⁻¹)) := hle ζ⁻¹
  have hEaS : E ζ⁻¹ ≤ Submodule.span (ZMod p) ({u, u'} : Set U) := by
    intro v hv
    exact mem_span_of_apply_eq_smul htform ht'form hζinv
      (Module.End.mem_eigenspace_iff.mp hv)
  have hEbS : E (ζ⁻¹ * ζ⁻¹) ≤ Submodule.span (ZMod p) ({u, u'} : Set U) := by
    intro v hv
    exact mem_span_of_apply_eq_smul htform ht'form hζinv2
      (Module.End.mem_eigenspace_iff.mp hv)
  have hdisj : E ζ⁻¹ ⊓ E (ζ⁻¹ * ζ⁻¹) = ⊥ :=
    zsc_eigenspaces_disjoint (Ne.symm hζdist)
  have hSdim : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({u, u'} : Set U)) ≤ 2 :=
    zsc_finrank_span_pair_le_two (wSlpmC_ne_zero hφ h2) (wSlpmC_ne_zero hψ h2)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (E ζ⁻¹) (E (ζ⁻¹ * ζ⁻¹))
  have hinf : Module.finrank (ZMod p) ↥(E ζ⁻¹ ⊓ E (ζ⁻¹ * ζ⁻¹)) = 0 := by
    rw [hdisj, finrank_bot]
  have hsupLe : Module.finrank (ZMod p) ↥(E ζ⁻¹ ⊔ E (ζ⁻¹ * ζ⁻¹)) ≤ 2 := by
    calc Module.finrank (ZMod p) ↥(E ζ⁻¹ ⊔ E (ζ⁻¹ * ζ⁻¹))
        ≤ Module.finrank (ZMod p) (Submodule.span (ZMod p) ({u, u'} : Set U)) :=
          Submodule.finrank_mono (sup_le hEaS hEbS)
      _ ≤ 2 := hSdim
  omega


omit [Module.Finite (ZMod p) U] in
private theorem zsc_eq_zero_of_neg_eq_self (h2 : (2 : ZMod p) ≠ 0) {x : U} (hx : -x = x) :
    x = 0 := by
  have h : x + x = 0 := by
    nth_rewrite 2 [← hx]
    exact add_neg_cancel x
  have h2x : (2 : ZMod p) • x = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.mp h2x).resolve_left h2

private theorem zsc_neg_one_ne_one (h2 : (2 : ZMod p) ≠ 0) : (-1 : ZMod p) ≠ 1 := by
  intro h
  apply h2
  have hzero : (1 : ZMod p) + 1 = 0 := by
    nth_rewrite 2 [h.symm]
    exact add_neg_cancel 1
  calc (2 : ZMod p) = 1 + 1 := by ring
    _ = 0 := hzero

omit [Module.Finite (ZMod p) U] in
private theorem zsc_commute_of_formula {a b : U} {α β : Dual (ZMod p) U}
    {r s : U ≃ₗ[ZMod p] U} (hr : ∀ x, r x = x - α x • a)
    (hs : ∀ x, s x = x - β x • b) (hab : α b = 0) (hba : β a = 0) : Commute r s := by
  rw [commute_iff_eq]
  ext x
  calc r (s x) = r (x - β x • b) := by rw [hs]
    _ = (x - β x • b) - α (x - β x • b) • a := by rw [hr]
    _ = x - β x • b - α x • a := by
          rw [map_sub, map_smul]
          simp [hab]
    _ = x - α x • a - β x • b := by abel
    _ = s (x - α x • a) := by
          rw [hs, map_sub, map_smul]
          simp [hba]
    _ = s (r x) := by rw [hr]

omit [Module.Finite (ZMod p) U] in
private theorem zsc_conj_apply {t : U ≃ₗ[ZMod p] U} {u : U} {φ : Dual (ZMod p) U}
    (hφ : φ u = 2) (ht : ∀ v, t v = v - φ v • u) (h : U ≃ₗ[ZMod p] U) (x : U) :
    (h * t * h⁻¹) x = x - (φ ∘ₗ (h.symm : U →ₗ[ZMod p] U)) x • h u := by
  have hteq : t = Module.reflection hφ := by
    ext v
    rw [ht v, Module.reflection_apply]
  have h' : (φ ∘ₗ (h.symm : U →ₗ[ZMod p] U)) (h u) = 2 := by
    simpa using hφ
  rw [hteq, conj_reflection h hφ h', Module.reflection_apply]

omit [Module.Finite (ZMod p) U] in
private theorem zsc_mem_map {P Q : Submodule (ZMod p) U} {e : U ≃ₗ[ZMod p] U}
    (hPQ : P.map (e : U →ₗ[ZMod p] U) = Q) {x : U} (hx : x ∈ P) : e x ∈ Q := by
  rw [← hPQ]
  exact Submodule.mem_map_of_mem hx

omit [Module.Finite (ZMod p) U] in
private theorem zsc_mem_of_apply_eq_self {G : Module.End (ZMod p) U}
    {S F : Submodule (ZMod p) U} (h2 : (2 : ZMod p) ≠ 0) (hF : ∀ x ∈ F, G x = x)
    (hS : ∀ x ∈ S, G x = -x) (hSF : S ⊔ F = ⊤) {y : U} (hy : G y = y) : y ∈ F := by
  have hySF : y ∈ S ⊔ F := by rw [hSF]; exact Submodule.mem_top
  obtain ⟨s, hsS, f, hfF, rfl⟩ := Submodule.mem_sup.mp hySF
  have hsum : G (s + f) = -s + f := by rw [map_add, hS s hsS, hF f hfF]
  rw [hy] at hsum
  have hneg : s = -s := add_right_cancel hsum
  have h2s : (2 : ZMod p) • s = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    exact add_neg_cancel s
  have hs0 : s = 0 := (smul_eq_zero.mp h2s).resolve_left h2
  rw [hs0, zero_add]
  exact hfF

private structure zsc_frame where
  hp : p ≠ 2
  t : U ≃ₗ[ZMod p] U
  t' : U ≃ₗ[ZMod p] U
  h : U ≃ₗ[ZMod p] U
  u : U
  u' : U
  φ : Dual (ZMod p) U
  ψ : Dual (ZMod p) U
  hφ : φ u = 2
  hψ : ψ u' = 2
  ht : ∀ v, t v = v - φ v • u
  ht' : ∀ v, t' v = v - ψ v • u'
  hcomm : Commute t t'
  hne : t ≠ t'
  hconj : ∀ v, h (t' (t v)) = -(t' (t (h v)))

private def zsc_frame.F (D : zsc_frame (p := p) (U := U)) : Submodule (ZMod p) U :=
  LinearMap.ker D.φ ⊓ LinearMap.ker D.ψ

private def zsc_frame.S (D : zsc_frame (p := p) (U := U)) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) ({D.u, D.u'} : Set U)

private def zsc_frame.G (D : zsc_frame (p := p) (U := U)) : Module.End (ZMod p) U :=
  (D.t' * D.t : U →ₗ[ZMod p] U)

private def zsc_frame.r (D : zsc_frame (p := p) (U := U)) : U ≃ₗ[ZMod p] U :=
  D.h * D.t * D.h⁻¹

private def zsc_frame.r' (D : zsc_frame (p := p) (U := U)) : U ≃ₗ[ZMod p] U :=
  D.h * D.t' * D.h⁻¹

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.teq (D : zsc_frame (p := p) (U := U)) : D.t = Module.reflection D.hφ := by
  ext v
  rw [D.ht v, Module.reflection_apply]

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.t'eq (D : zsc_frame (p := p) (U := U)) :
    D.t' = Module.reflection D.hψ := by
  ext v
  rw [D.ht' v, Module.reflection_apply]

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.φu' (D : zsc_frame (p := p) (U := U)) : D.φ D.u' = 0 := by
  have hcommR : Commute (Module.reflection D.hφ) (Module.reflection D.hψ) := by
    rw [← zsc_frame.teq D, ← zsc_frame.t'eq D]
    exact D.hcomm
  have hneR : Module.reflection D.hφ ≠ Module.reflection D.hψ := by
    rw [← zsc_frame.teq D, ← zsc_frame.t'eq D]
    exact D.hne
  exact apply_eq_zero_of_commute D.hp D.hφ D.hψ hcommR hneR

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.ψu (D : zsc_frame (p := p) (U := U)) : D.ψ D.u = 0 := by
  have hcommR : Commute (Module.reflection D.hφ) (Module.reflection D.hψ) := by
    rw [← zsc_frame.teq D, ← zsc_frame.t'eq D]
    exact D.hcomm
  have hneR : Module.reflection D.hφ ≠ Module.reflection D.hψ := by
    rw [← zsc_frame.teq D, ← zsc_frame.t'eq D]
    exact D.hne
  exact apply_eq_zero_of_commute D.hp (a := D.u') (b := D.u) (φ := D.ψ) (ψ := D.φ)
    D.hψ D.hφ hcommR.symm hneR.symm

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.linearIndependent (D : zsc_frame (p := p) (U := U)) :
    LinearIndependent (ZMod p) ![D.u, D.u'] := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero D.hp
  have hu0 : D.u ≠ 0 := wSlpmC_ne_zero D.hφ h2
  rw [LinearIndependent.pair_iff' hu0]
  intro c hc
  have hφc : D.φ (c • D.u) = D.φ D.u' := by rw [hc]
  rw [map_smul, D.hφ, zsc_frame.φu' D, smul_eq_mul] at hφc
  have hc0 : c = 0 := (mul_eq_zero.mp hφc).resolve_right h2
  rw [hc0, zero_smul] at hc
  exact (wSlpmC_ne_zero D.hψ h2) hc.symm

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.S_finrank (D : zsc_frame (p := p) (U := U)) :
    Module.finrank (ZMod p) D.S = 2 := by
  have hLI := zsc_frame.linearIndependent D
  have hrange : (Set.range ![D.u, D.u'] : Set U) = {D.u, D.u'} := by
    ext x
    simp [or_comm]
  rw [zsc_frame.S, ← hrange, finrank_span_eq_card hLI]
  simp

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.S_inf_F (D : zsc_frame (p := p) (U := U)) : D.S ⊓ D.F = ⊥ := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero D.hp
  refine eq_bot_iff.mpr ?_
  intro x hx
  obtain ⟨hxS, hxF⟩ := hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hxS
  have hφx : D.φ (a • D.u + b • D.u') = 0 := hxF.1
  have hψx : D.ψ (a • D.u + b • D.u') = 0 := hxF.2
  rw [map_add, map_smul, map_smul, D.hφ, zsc_frame.φu' D, smul_eq_mul, smul_eq_mul,
    mul_zero, add_zero] at hφx
  rw [map_add, map_smul, map_smul, zsc_frame.ψu D, D.hψ, smul_eq_mul, smul_eq_mul,
    mul_zero, zero_add] at hψx
  have ha : a = 0 := (mul_eq_zero.mp hφx).resolve_right h2
  have hb : b = 0 := (mul_eq_zero.mp hψx).resolve_right h2
  rw [ha, hb, zero_smul, zero_smul, add_zero]
  exact Submodule.zero_mem _


private theorem zsc_frame.dim_data (D : zsc_frame (p := p) (U := U))
    (hSdim : Module.finrank (ZMod p) D.S = 2)
    (hFdim : Module.finrank (ZMod p) U - 2 ≤ Module.finrank (ZMod p) D.F)
    (hSF : D.S ⊓ D.F = ⊥) :
    D.S ⊔ D.F = ⊤ ∧ Module.finrank (ZMod p) D.F = Module.finrank (ZMod p) U - 2 := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq D.S D.F
  rw [hSF, finrank_bot, add_zero] at hsup
  have hle : Module.finrank (ZMod p) ↥(D.S ⊔ D.F) ≤ Module.finrank (ZMod p) U :=
    Submodule.finrank_le _
  have hFfin : Module.finrank (ZMod p) D.F = Module.finrank (ZMod p) U - 2 := by omega
  have htop : D.S ⊔ D.F = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hsup, hSdim]
    omega
  exact ⟨htop, hFfin⟩

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.fixed_data (D : zsc_frame (p := p) (U := U)) :
    (∀ x ∈ D.F, D.G x = x) ∧ (∀ x ∈ D.S, D.G x = -x) := by
  have hGF : ∀ x ∈ D.F, D.G x = x := by
    intro x hx
    exact apply_eq_self_of_mem_ker_inf D.ht D.ht' hx
  have hgu : D.G D.u = -D.u := by
    have htu : D.t D.u = -D.u := wSlpmC_of_refl_a D.hφ D.t D.ht
    have hmem : D.u ∈ LinearMap.ker D.ψ := by
      rw [LinearMap.mem_ker]
      exact zsc_frame.ψu D
    have ht'u : D.t' D.u = D.u := wSlpmC_of_refl_ker D.t' D.ht' ⟨D.u, hmem⟩
    calc D.G D.u = (D.t' * D.t : Module.End (ZMod p) U) D.u := rfl
      _ = D.t' (D.t D.u) := rfl
      _ = D.t' (-D.u) := by rw [htu]
      _ = -D.t' D.u := map_neg D.t' D.u
      _ = -D.u := by rw [ht'u]
  have hgu' : D.G D.u' = -D.u' := by
    have hmem : D.u' ∈ LinearMap.ker D.φ := by
      rw [LinearMap.mem_ker]
      exact zsc_frame.φu' D
    have htu' : D.t D.u' = D.u' := wSlpmC_of_refl_ker D.t D.ht ⟨D.u', hmem⟩
    calc D.G D.u' = (D.t' * D.t : Module.End (ZMod p) U) D.u' := rfl
      _ = D.t' (D.t D.u') := rfl
      _ = D.t' D.u' := by rw [htu']
      _ = -D.u' := wSlpmC_of_refl_a D.hψ D.t' D.ht'
  have hSle : D.S ≤ Module.End.eigenspace D.G (-1) := by
    rw [zsc_frame.S, Submodule.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Module.End.mem_eigenspace_iff.mpr (by simpa using hgu)
    · exact Module.End.mem_eigenspace_iff.mpr (by simpa using hgu')
  refine ⟨hGF, fun x hx => ?_⟩
  have h := Module.End.mem_eigenspace_iff.mp (hSle hx)
  simpa using h


omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.map_le (D : zsc_frame (p := p) (U := U))
    (hSF_top : D.S ⊔ D.F = ⊤) :
    D.F.map (D.h : U →ₗ[ZMod p] U) ≤ D.S ∧ D.S.map (D.h : U →ₗ[ZMod p] U) ≤ D.F := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero D.hp
  have hneg1 : (-1 : ZMod p) ≠ 1 := zsc_neg_one_ne_one h2
  obtain ⟨hGF, hSneg⟩ := zsc_frame.fixed_data D
  constructor
  · rintro _ ⟨x, hxF, rfl⟩
    have hx : D.G x = x := hGF x hxF
    have hx' : D.t' (D.t x) = x := hx
    have h1 : D.t' (D.t (D.h x)) = -D.h x := by
      have hc := D.hconj x
      rw [hx'] at hc
      simpa using (congrArg Neg.neg hc).symm
    have h1' : D.t' (D.t (D.h x)) = (-1 : ZMod p) • D.h x := by
      rw [neg_one_smul]
      exact h1
    exact mem_span_of_apply_eq_smul D.ht D.ht' hneg1 h1'
  · rintro _ ⟨x, hxS, rfl⟩
    have hx : D.G x = -x := hSneg x hxS
    have hx' : D.t' (D.t x) = -x := hx
    have h1 : D.t' (D.t (D.h x)) = D.h x := by
      have hc := D.hconj x
      rw [hx', map_neg] at hc
      exact (neg_injective hc).symm
    exact zsc_mem_of_apply_eq_self h2 hGF hSneg hSF_top h1

private theorem zsc_frame.map_data (D : zsc_frame (p := p) (U := U))
    (hF_le_S : D.F.map (D.h : U →ₗ[ZMod p] U) ≤ D.S)
    (hS_le_F : D.S.map (D.h : U →ₗ[ZMod p] U) ≤ D.F)
    (hSdim : Module.finrank (ZMod p) D.S = 2)
    (hFfin : Module.finrank (ZMod p) D.F = Module.finrank (ZMod p) U - 2)
    (hn4 : Module.finrank (ZMod p) U = 4) :
    D.S.map (D.h : U →ₗ[ZMod p] U) = D.F ∧
      D.F.map (D.h : U →ₗ[ZMod p] U) = D.S ∧
      D.F.map (D.h.symm : U →ₗ[ZMod p] U) = D.S ∧
      D.S.map (D.h.symm : U →ₗ[ZMod p] U) = D.F := by
  have hSmapF : D.S.map (D.h : U →ₗ[ZMod p] U) = D.F := by
    refine Submodule.eq_of_le_of_finrank_le hS_le_F ?_
    rw [LinearEquiv.finrank_map_eq D.h D.S, hSdim, hFfin, hn4]
  have hFmapS : D.F.map (D.h : U →ₗ[ZMod p] U) = D.S := by
    refine Submodule.eq_of_le_of_finrank_le hF_le_S ?_
    rw [LinearEquiv.finrank_map_eq D.h D.F, hFfin, hn4, hSdim]
  have hFmapSinv : D.F.map (D.h.symm : U →ₗ[ZMod p] U) = D.S :=
    (Submodule.map_symm_eq_iff (e := D.h)).mpr hSmapF
  have hSmapFinv : D.S.map (D.h.symm : U →ₗ[ZMod p] U) = D.F :=
    (Submodule.map_symm_eq_iff (e := D.h)).mpr hFmapS
  exact ⟨hSmapF, hFmapS, hFmapSinv, hSmapFinv⟩


omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.mem_data (D : zsc_frame (p := p) (U := U))
    (hSmapF : D.S.map (D.h : U →ₗ[ZMod p] U) = D.F)
    (hSmapFinv : D.S.map (D.h.symm : U →ₗ[ZMod p] U) = D.F) :
    D.φ (D.h D.u) = 0 ∧ D.ψ (D.h D.u) = 0 ∧ D.φ (D.h D.u') = 0 ∧
      D.ψ (D.h D.u') = 0 ∧ D.φ ((D.h.symm : U →ₗ[ZMod p] U) D.u) = 0 ∧
      D.ψ ((D.h.symm : U →ₗ[ZMod p] U) D.u) = 0 ∧
      D.φ ((D.h.symm : U →ₗ[ZMod p] U) D.u') = 0 ∧
      D.ψ ((D.h.symm : U →ₗ[ZMod p] U) D.u') = 0 := by
  have huS : D.u ∈ D.S := by
    rw [zsc_frame.S]
    exact Submodule.subset_span (by simp)
  have hu'S : D.u' ∈ D.S := by
    rw [zsc_frame.S]
    exact Submodule.subset_span (by simp)
  have key : ∀ {x : U}, x ∈ D.S → D.φ (D.h x) = 0 ∧ D.ψ (D.h x) = 0 := by
    intro x hx
    exact zsc_mem_map (P := D.S) (Q := D.F) hSmapF hx
  have keyinv : ∀ {x : U}, x ∈ D.S → D.φ ((D.h.symm : U →ₗ[ZMod p] U) x) = 0 ∧
      D.ψ ((D.h.symm : U →ₗ[ZMod p] U) x) = 0 := by
    intro x hx
    exact zsc_mem_map (P := D.S) (Q := D.F) hSmapFinv hx
  obtain ⟨hφhu, hψhu⟩ := key huS
  obtain ⟨hφhu', hψhu'⟩ := key hu'S
  obtain ⟨hφhinu, hψhinu⟩ := keyinv huS
  obtain ⟨hφhinu', hψhinu'⟩ := keyinv hu'S
  exact ⟨hφhu, hψhu, hφhu', hψhu', hφhinu, hψhinu, hφhinu', hψhinu'⟩

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.commute_data (D : zsc_frame (p := p) (U := U))
    (hSmapF : D.S.map (D.h : U →ₗ[ZMod p] U) = D.F)
    (hSmapFinv : D.S.map (D.h.symm : U →ₗ[ZMod p] U) = D.F) :
    Pairwise (fun i j => Commute (![D.t, D.t', D.r, D.r'] i) (![D.t, D.t', D.r, D.r'] j)) := by
  obtain ⟨hφhu, hψhu, hφhu', hψhu', hφhinu, hψhinu, hφhinu', hψhinu'⟩ :=
    zsc_frame.mem_data D hSmapF hSmapFinv
  have hr : ∀ x, D.r x = x - (D.φ ∘ₗ (D.h.symm : U →ₗ[ZMod p] U)) x • D.h D.u :=
    zsc_conj_apply D.hφ D.ht D.h
  have hr' : ∀ x, D.r' x = x - (D.ψ ∘ₗ (D.h.symm : U →ₗ[ZMod p] U)) x • D.h D.u' :=
    zsc_conj_apply D.hψ D.ht' D.h
  have h01 : Commute D.t D.t' := D.hcomm
  have h02 : Commute D.t D.r :=
    (zsc_commute_of_formula (s := D.t) hr D.ht (by simpa using hφhinu) hφhu).symm
  have h03 : Commute D.t D.r' :=
    (zsc_commute_of_formula (s := D.t) hr' D.ht (by simpa using hψhinu) hφhu').symm
  have h12 : Commute D.t' D.r :=
    (zsc_commute_of_formula (s := D.t') hr D.ht' (by simpa using hφhinu') hψhu).symm
  have h13 : Commute D.t' D.r' :=
    (zsc_commute_of_formula (s := D.t') hr' D.ht' (by simpa using hψhinu') hψhu').symm
  have h23 : Commute D.r D.r' :=
    zsc_commute_of_formula hr hr' (by simpa using zsc_frame.φu' D)
      (by simpa using zsc_frame.ψu D)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact h01 | exact h01.symm | exact h02 | exact h02.symm
      | exact h03 | exact h03.symm | exact h12 | exact h12.symm
      | exact h13 | exact h13.symm | exact h23 | exact h23.symm
      | exact absurd rfl hij

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.eval_data (D : zsc_frame (p := p) (U := U))
    (hSmapF : D.S.map (D.h : U →ₗ[ZMod p] U) = D.F)
    (hSmapFinv : D.S.map (D.h.symm : U →ₗ[ZMod p] U) = D.F) :
    D.r D.u = D.u ∧ D.r D.u' = D.u' ∧ D.r' D.u = D.u ∧
      D.r' (D.h D.u') = -D.h D.u' ∧ D.r (D.h D.u') = D.h D.u' ∧ D.h D.u' ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero D.hp
  obtain ⟨hφhu, hψhu, hφhu', hψhu', hφhinu, hψhinu, hφhinu', hψhinu'⟩ :=
    zsc_frame.mem_data D hSmapF hSmapFinv
  have hr : ∀ x, D.r x = x - (D.φ ∘ₗ (D.h.symm : U →ₗ[ZMod p] U)) x • D.h D.u :=
    zsc_conj_apply D.hφ D.ht D.h
  have hr' : ∀ x, D.r' x = x - (D.ψ ∘ₗ (D.h.symm : U →ₗ[ZMod p] U)) x • D.h D.u' :=
    zsc_conj_apply D.hψ D.ht' D.h
  have hhu'0 : D.h D.u' ≠ 0 := by
    intro h0
    exact (wSlpmC_ne_zero D.hψ h2) (D.h.injective (by rw [h0, map_zero]))
  have hru : D.r D.u = D.u := by
    rw [hr D.u, LinearMap.comp_apply, hφhinu, zero_smul, sub_zero]
  have hru' : D.r D.u' = D.u' := by
    rw [hr D.u', LinearMap.comp_apply, hφhinu', zero_smul, sub_zero]
  have hr'u : D.r' D.u = D.u := by
    rw [hr' D.u, LinearMap.comp_apply, hψhinu, zero_smul, sub_zero]
  have hr'hu' : D.r' (D.h D.u') = -D.h D.u' := by
    rw [hr' (D.h D.u'), LinearMap.comp_apply]
    change D.h D.u' - D.ψ (D.h.symm (D.h D.u')) • D.h D.u' = -D.h D.u'
    rw [D.h.symm_apply_apply, D.hψ, two_smul]
    abel
  have hrhu' : D.r (D.h D.u') = D.h D.u' := by
    rw [hr (D.h D.u'), LinearMap.comp_apply]
    change D.h D.u' - D.φ (D.h.symm (D.h D.u')) • D.h D.u = D.h D.u'
    rw [D.h.symm_apply_apply, zsc_frame.φu' D, zero_smul, sub_zero]
  exact ⟨hru, hru', hr'u, hr'hu', hrhu', hhu'0⟩

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.ne_data_left (D : zsc_frame (p := p) (U := U))
    (hru : D.r D.u = D.u) (hru' : D.r D.u' = D.u') (hr'u : D.r' D.u = D.u) :
    D.t ≠ D.r ∧ D.t' ≠ D.r ∧ D.t ≠ D.r' := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero D.hp
  have hne_t_r : D.t ≠ D.r := by
    intro heq
    have h1 : -D.u = D.u := by
      calc -D.u = D.t D.u := (wSlpmC_of_refl_a D.hφ D.t D.ht).symm
        _ = D.r D.u := by rw [heq]
        _ = D.u := hru
    exact (wSlpmC_ne_zero D.hφ h2) (zsc_eq_zero_of_neg_eq_self h2 h1)
  have hne_t'_r : D.t' ≠ D.r := by
    intro heq
    have h1 : -D.u' = D.u' := by
      calc -D.u' = D.t' D.u' := (wSlpmC_of_refl_a D.hψ D.t' D.ht').symm
        _ = D.r D.u' := by rw [heq]
        _ = D.u' := hru'
    exact (wSlpmC_ne_zero D.hψ h2) (zsc_eq_zero_of_neg_eq_self h2 h1)
  have hne_t_r' : D.t ≠ D.r' := by
    intro heq
    have h1 : -D.u = D.u := by
      calc -D.u = D.t D.u := (wSlpmC_of_refl_a D.hφ D.t D.ht).symm
        _ = D.r' D.u := by rw [heq]
        _ = D.u := hr'u
    exact (wSlpmC_ne_zero D.hφ h2) (zsc_eq_zero_of_neg_eq_self h2 h1)
  exact ⟨hne_t_r, hne_t'_r, hne_t_r'⟩

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.ne_data_right (D : zsc_frame (p := p) (U := U))
    (hψhu' : D.ψ (D.h D.u') = 0) (hhu'0 : D.h D.u' ≠ 0)
    (hr'hu' : D.r' (D.h D.u') = -D.h D.u') (hrhu' : D.r (D.h D.u') = D.h D.u') :
    D.t' ≠ D.r' ∧ D.r ≠ D.r' := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero D.hp
  have hne_t'_r' : D.t' ≠ D.r' := by
    intro heq
    have h1 : D.h D.u' = -D.h D.u' := by
      calc D.h D.u' = D.t' (D.h D.u') := by
            rw [wSlpmC_of_refl_ker D.t' D.ht'
              (⟨D.h D.u', by rw [LinearMap.mem_ker]; exact hψhu'⟩ :
                ↥(LinearMap.ker D.ψ))]
        _ = D.r' (D.h D.u') := by rw [heq]
        _ = -D.h D.u' := hr'hu'
    exact hhu'0 (zsc_eq_zero_of_neg_eq_self h2 h1.symm)
  have hne_r_r' : D.r ≠ D.r' := by
    intro heq
    have h1 : -D.h D.u' = D.h D.u' := by
      calc -D.h D.u' = D.r' (D.h D.u') := hr'hu'.symm
        _ = D.r (D.h D.u') := by rw [heq]
        _ = D.h D.u' := hrhu'
    exact hhu'0 (zsc_eq_zero_of_neg_eq_self h2 h1)
  exact ⟨hne_t'_r', hne_r_r'⟩

omit [Module.Finite (ZMod p) U] in
private theorem zsc_frame.injective_data (D : zsc_frame (p := p) (U := U))
    (hSmapF : D.S.map (D.h : U →ₗ[ZMod p] U) = D.F)
    (hSmapFinv : D.S.map (D.h.symm : U →ₗ[ZMod p] U) = D.F) :
    Function.Injective ![D.t, D.t', D.r, D.r'] := by
  obtain ⟨hru, hru', hr'u, hr'hu', hrhu', hhu'0⟩ :=
    zsc_frame.eval_data D hSmapF hSmapFinv
  obtain ⟨-, -, -, hψhu', -, -, -, -⟩ := zsc_frame.mem_data D hSmapF hSmapFinv
  obtain ⟨hne_t_r, hne_t'_r, hne_t_r'⟩ := zsc_frame.ne_data_left D hru hru' hr'u
  obtain ⟨hne_t'_r', hne_r_r'⟩ := zsc_frame.ne_data_right D hψhu' hhu'0 hr'hu' hrhu'
  rw [Function.Injective]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | exact absurd hij D.hne | exact absurd hij.symm D.hne
      | exact absurd hij hne_t_r | exact absurd hij.symm hne_t_r
      | exact absurd hij hne_t'_r | exact absurd hij.symm hne_t'_r
      | exact absurd hij hne_t_r' | exact absurd hij.symm hne_t_r'
      | exact absurd hij hne_t'_r' | exact absurd hij.symm hne_t'_r'
      | exact absurd hij hne_r_r' | exact absurd hij.symm hne_r_r'

theorem frame_of_apply_mul_eq_neg (hp : p ≠ 2) {t t' h : U ≃ₗ[ZMod p] U}
    (ht : IsRefl p t) (ht' : IsRefl p t') (hcomm : Commute t t') (hne : t ≠ t')
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    (hconj : ∀ v, h (t' (t v)) = -(t' (t (h v)))) :
    Module.finrank (ZMod p) U = 4 ∧
      Pairwise (fun i j => Commute (![t, t', h * t * h⁻¹, h * t' * h⁻¹] i)
        (![t, t', h * t * h⁻¹, h * t' * h⁻¹] j)) ∧
      Function.Injective ![t, t', h * t * h⁻¹, h * t' * h⁻¹] := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  obtain ⟨u, φ, hφ, htform⟩ := wSlpmC_isRefl_form h2 t ht
  obtain ⟨u', ψ, hψ, ht'form⟩ := wSlpmC_isRefl_form h2 t' ht'
  let D : zsc_frame (p := p) (U := U) :=
    { hp := hp, t := t, t' := t', h := h, u := u, u' := u', φ := φ, ψ := ψ,
      hφ := hφ, hψ := hψ, ht := htform, ht' := ht'form, hcomm := hcomm, hne := hne,
      hconj := hconj }
  have hFdim : Module.finrank (ZMod p) U - 2 ≤ Module.finrank (ZMod p) D.F :=
    finrank_ker_inf_ge D.hφ D.hψ h2
  have hSdim : Module.finrank (ZMod p) D.S = 2 := zsc_frame.S_finrank D
  have hSF_inf : D.S ⊓ D.F = ⊥ := zsc_frame.S_inf_F D
  obtain ⟨hSF_top, hFfin⟩ := zsc_frame.dim_data D hSdim hFdim hSF_inf
  obtain ⟨hF_le_S, hS_le_F⟩ := zsc_frame.map_le D hSF_top
  have hFle2 : Module.finrank (ZMod p) D.F ≤ 2 := by
    calc Module.finrank (ZMod p) D.F
        = Module.finrank (ZMod p) (D.F.map (D.h : U →ₗ[ZMod p] U)) :=
          (LinearEquiv.finrank_map_eq D.h D.F).symm
      _ ≤ Module.finrank (ZMod p) D.S := Submodule.finrank_mono hF_le_S
      _ = 2 := hSdim
  have hn4 : Module.finrank (ZMod p) U = 4 := by omega
  obtain ⟨hSmapF, hFmapS, hFmapSinv, hSmapFinv⟩ :=
    zsc_frame.map_data D hF_le_S hS_le_F hSdim hFfin hn4
  exact ⟨hn4, zsc_frame.commute_data D hSmapF hSmapFinv,
    zsc_frame.injective_data D hSmapF hSmapFinv⟩

end CFSG.StandardType.ZS
