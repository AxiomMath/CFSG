module

public import Mathlib.GroupTheory.Focal

public section

namespace CFSG

open scoped commutatorElement

section
open Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

open Subgroup in
theorem _root_.Subgroup.focalSubgroup_eq_closure_isConj :
    H.focalSubgroup = closure {z : G | ∃ x ∈ H, ∃ y ∈ H, IsConj x y ∧ z = x⁻¹ * y} := by
  rw [focalSubgroup_def]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, x, hx, u, rfl⟩
    refine ⟨x⁻¹, H.inv_mem hx, u * x⁻¹ * u⁻¹, ?_, ?_, ?_⟩
    · have : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact H.mul_mem (H.inv_mem hx) hz
    · exact isConj_iff.mpr ⟨u, rfl⟩
    · simp [commutatorElement_def, mul_assoc]
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
    refine ⟨H.mul_mem (H.inv_mem hx) hy, x⁻¹, H.inv_mem hx, c, ?_⟩
    simp [commutatorElement_def, mul_assoc]

end

end CFSG
