module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import Mathlib.LinearAlgebra.Reflection
import CFSG.LocalAnalysis.StandardType.GGWitSlpmConjAux
import TauCeti.LinearAlgebra.Reflection
import CFSG.LocalAnalysis.StandardType.GGWitSlpm

public section

namespace CFSG.StandardType.ZS

open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem isRefl_reflection (hp : p ≠ 2) {a : U} {φ : Dual (ZMod p) U} (hφ : φ a = 2) :
    IsRefl p (reflection hφ) := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have ha : a ≠ 0 := fun h => h2 (by rw [h, map_zero] at hφ; exact hφ.symm)
  refine ⟨?_, ?_⟩
  · simpa [Module.reflection_inv] using mul_inv_cancel (Module.reflection hφ)
  · have hrange : LinearMap.range
        ((Module.reflection hφ : U →ₗ[ZMod p] U) - LinearMap.id) =
        Submodule.span (ZMod p) {a} := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        change Module.reflection hφ v - v ∈ Submodule.span (ZMod p) {a}
        have hv : Module.reflection hφ v - v = -(φ v • a) := by
          rw [Module.reflection_apply]
          abel
        rw [hv]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ (φ v)
          (Submodule.subset_span (Set.mem_singleton a)))
      · rw [Submodule.span_singleton_le_iff_mem]
        have hmem : -a ∈ LinearMap.range
            ((Module.reflection hφ : U →ₗ[ZMod p] U) - LinearMap.id) := by
          refine ⟨(2 : ZMod p)⁻¹ • a, ?_⟩
          have hφv : φ ((2 : ZMod p)⁻¹ • a) = 1 := by
            rw [map_smul, hφ, smul_eq_mul, inv_mul_cancel₀ h2]
          change Module.reflection hφ ((2 : ZMod p)⁻¹ • a) - (2 : ZMod p)⁻¹ • a = -a
          rw [show Module.reflection hφ ((2 : ZMod p)⁻¹ • a) - (2 : ZMod p)⁻¹ • a
              = -(φ ((2 : ZMod p)⁻¹ • a) • a) by rw [Module.reflection_apply]; abel]
          rw [hφv, one_smul]
        simpa using Submodule.neg_mem _ hmem
    rw [hrange, finrank_span_singleton ha]

theorem isRefl_iff [Module.Finite (ZMod p) U] (hp : p ≠ 2) (t : U ≃ₗ[ZMod p] U) :
    IsRefl p t ↔ ∃ (a : U) (φ : Dual (ZMod p) U) (hφ : φ a = 2), t = reflection hφ := by
  constructor
  · intro ht
    obtain ⟨a, φ, hφ, hφv⟩ := wSlpmC_isRefl_form (wSlpmC_two_ne_zero hp) t ht
    exact ⟨a, φ, hφ, LinearEquiv.ext fun v => by rw [hφv v, Module.reflection_apply]⟩
  · rintro ⟨a, φ, hφ, rfl⟩
    exact isRefl_reflection hp hφ

theorem det_eq_neg_one_of_isRefl [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) : LinearEquiv.det t = -1 := by
  obtain ⟨a, φ, hφ, rfl⟩ := (isRefl_iff hp t).mp ht
  exact Module.det_reflection hφ

end CFSG.StandardType.ZS
