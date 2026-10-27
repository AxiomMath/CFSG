module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH

variable {V : Type*} [CommGroup V]

theorem isTranspAxis_one (U W : Subgroup V) : IsTranspAxis (1 : MulAut V) U W 1 := by
  constructor
  · intro x hx
    rw [MulAut.one_apply]
    simpa using Subgroup.one_mem U
  · intro x hx
    rw [MulAut.one_apply]
    simpa using Subgroup.one_mem U

theorem isTranspAxis_mul {U W : Subgroup V} (hUW : U ≤ W) {g₁ g₂ : MulAut V} {c₁ c₂ : V}
    (hc₂ : c₂ ∈ W) (h₁ : IsTranspAxis g₁ U W c₁) (h₂ : IsTranspAxis g₂ U W c₂) :
    IsTranspAxis (g₁ * g₂) U W (c₁ * c₂) := by
  constructor
  · intro x hx
    rw [MulAut.mul_apply]
    have hg2x : g₂ x ∈ W := by
      have hu : g₂ x * x⁻¹ ∈ U := h₂.1 x hx
      have hprod : (g₂ x * x⁻¹) * x ∈ W := Subgroup.mul_mem W (hUW hu) hx
      convert hprod using 1
      simp [mul_comm, mul_left_comm, mul_assoc]
    have hb : g₁ (g₂ x) * (g₂ x)⁻¹ ∈ U := h₁.1 (g₂ x) hg2x
    have ha : g₂ x * x⁻¹ ∈ U := h₂.1 x hx
    convert Subgroup.mul_mem U hb ha using 1
    simp [mul_comm, mul_left_comm, mul_assoc]
  · intro x hx
    rw [MulAut.mul_apply]
    have hg2x : g₂ x ∉ W := by
      intro hg
      have hu : g₂ x * x⁻¹ * c₂⁻¹ ∈ U := h₂.2 x hx
      apply hx
      rw [show x = g₂ x * c₂⁻¹ * (g₂ x * x⁻¹ * c₂⁻¹)⁻¹ by
        simp [mul_comm, mul_left_comm, mul_assoc]]
      exact Subgroup.mul_mem W (Subgroup.mul_mem W hg (Subgroup.inv_mem W hc₂))
        (Subgroup.inv_mem W (hUW hu))
    have hb : g₁ (g₂ x) * (g₂ x)⁻¹ * c₁⁻¹ ∈ U := h₁.2 (g₂ x) hg2x
    have ha : g₂ x * x⁻¹ * c₂⁻¹ ∈ U := h₂.2 x hx
    convert Subgroup.mul_mem U hb ha using 1
    simp [mul_comm, mul_left_comm, mul_assoc]

theorem isTranspAxis_congr_center {U W : Subgroup V} {g : MulAut V} {c c' : V}
    (h : IsTranspAxis g U W c) (hc : c' * c⁻¹ ∈ U) : IsTranspAxis g U W c' := by
  constructor
  · exact h.1
  · intro x hx
    have hbase : g x * x⁻¹ * c⁻¹ ∈ U := h.2 x hx
    have hmem : (c' * c⁻¹)⁻¹ ∈ U := Subgroup.inv_mem U hc
    convert Subgroup.mul_mem U hbase hmem using 1
    simp [mul_comm, mul_left_comm, mul_assoc]

theorem isTranspAxis_center_unique {U W : Subgroup V} {g : MulAut V} {c c' x : V} (hx : x ∉ W)
    (h : IsTranspAxis g U W c) (h' : IsTranspAxis g U W c') : c * c'⁻¹ ∈ U := by
  have h1 : g x * x⁻¹ * c⁻¹ ∈ U := h.2 x hx
  have h2 : g x * x⁻¹ * c'⁻¹ ∈ U := h'.2 x hx
  convert Subgroup.mul_mem U h2 (Subgroup.inv_mem U h1) using 1
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem isTranspAxis_conj {U W : Subgroup V} {g h : MulAut V} {c : V}
    (hU : ∀ u ∈ U, h u ∈ U) (hW : ∀ x, x ∈ W ↔ h x ∈ W) (hg : IsTranspAxis g U W c) :
    IsTranspAxis (h * g * h⁻¹) U W (h c) := by
  constructor
  · intro x hx
    set y : V := h⁻¹ x with hy
    have hyx : h y = x := by rw [hy, MulAut.apply_inv_self]
    have hyW : y ∈ W := by
      rw [hW]
      rw [hyx]
      exact hx
    have hmem : g y * y⁻¹ ∈ U := hg.1 y hyW
    have h1 : (h * g * h⁻¹) x = h (g y) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, ← hy]
    have h2 : x⁻¹ = h (y⁻¹) := by
      rw [← hyx, map_inv]
    have heq : (h * g * h⁻¹) x * x⁻¹ = h (g y * y⁻¹) := by
      rw [h1, h2]
      simp only [map_mul, map_inv]
    rw [heq]
    exact hU _ hmem
  · intro x hx
    set y : V := h⁻¹ x with hy
    have hyx : h y = x := by rw [hy, MulAut.apply_inv_self]
    have hyW : y ∉ W := by
      rw [hW]
      rw [hyx]
      exact hx
    have hmem : g y * y⁻¹ * c⁻¹ ∈ U := hg.2 y hyW
    have h1 : (h * g * h⁻¹) x = h (g y) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, ← hy]
    have h2 : x⁻¹ = h (y⁻¹) := by
      rw [← hyx, map_inv]
    have h3 : (h c)⁻¹ = h (c⁻¹) := by rw [map_inv]
    have heq : (h * g * h⁻¹) x * x⁻¹ * (h c)⁻¹ = h (g y * y⁻¹ * c⁻¹) := by
      rw [h1, h2, h3]
      simp only [map_mul, map_inv]
    rw [heq]
    exact hU _ hmem

end CFSG.ASVolI.H16
