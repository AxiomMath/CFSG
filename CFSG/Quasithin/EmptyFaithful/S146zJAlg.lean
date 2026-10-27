module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin

section Fix

@[expose] def fixSubOf {V : Type*} [Group V] (σ : MulAut V) : Subgroup V where
  carrier := {w | σ w = w}
  mul_mem' := fun {a b} ha hb => by
    show σ (a * b) = a * b
    rw [map_mul]
    exact congrArg₂ (· * ·) ha hb
  one_mem' := map_one σ
  inv_mem' := fun {a} ha => by
    show σ a⁻¹ = a⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) ha

theorem card_fix_sq_le {V : Type*} [CommGroup V] [Finite V] (α σ : MulAut V) (W : Subgroup V)
    (hαW : ∀ w ∈ W, α w ∈ W) (hα2 : ∀ w ∈ W, α (α w) = w → w = 1)
    (hinv : ∀ w ∈ W, α (σ (α w)) = σ w) :
    Nat.card ↥(fixSubOf σ ⊓ W) * Nat.card ↥(fixSubOf σ ⊓ W) ≤ Nat.card W := by
  classical
  let C : Subgroup V := fixSubOf σ ⊓ W
  have hCW : ∀ c ∈ C, c ∈ W := fun c hc => hc.2
  have hCσ : ∀ c ∈ C, σ c = c := fun c hc => hc.1
  let Φ : C × C → W := fun cc =>
    ⟨(cc.1 : V) * α (cc.2 : V), W.mul_mem (hCW _ cc.1.2) (hαW _ (hCW _ cc.2.2))⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨c₁, c₁'⟩ ⟨c₂, c₂'⟩ h
    have h' : (c₁ : V) * α (c₁' : V) = (c₂ : V) * α (c₂' : V) := congrArg Subtype.val h
    have h2 : (c₁ : V) * (c₂ : V)⁻¹ = α (c₂' : V) * (α (c₁' : V))⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, mul_comm (α _) _]
      exact h'
    have huC : (c₁ : V) * (c₂ : V)⁻¹ ∈ C := C.mul_mem c₁.2 (C.inv_mem c₂.2)
    have hu'C : (c₂' : V) * (c₁' : V)⁻¹ ∈ C := C.mul_mem c₂'.2 (C.inv_mem c₁'.2)
    have hα : (c₁ : V) * (c₂ : V)⁻¹ = α ((c₂' : V) * (c₁' : V)⁻¹) := by
      rw [map_mul, map_inv]
      exact h2
    have hW' : (c₂' : V) * (c₁' : V)⁻¹ ∈ W := hCW _ hu'C
    have hσu : σ ((c₁ : V) * (c₂ : V)⁻¹) = (c₁ : V) * (c₂ : V)⁻¹ := hCσ _ huC
    have hσu' : σ ((c₂' : V) * (c₁' : V)⁻¹) = (c₂' : V) * (c₁' : V)⁻¹ := hCσ _ hu'C
    have h1 := hinv _ hW'
    rw [← hα, hσu, hσu'] at h1
    have h3 : α (α ((c₂' : V) * (c₁' : V)⁻¹)) = (c₂' : V) * (c₁' : V)⁻¹ := by
      rw [← hα]
      exact h1
    have hu'1 : (c₂' : V) * (c₁' : V)⁻¹ = 1 := hα2 _ hW' h3
    have hu1 : (c₁ : V) * (c₂ : V)⁻¹ = 1 := by rw [hα, hu'1, map_one]
    have e1 : c₁ = c₂ := Subtype.ext (mul_inv_eq_one.mp hu1)
    have e2 : c₁' = c₂' := Subtype.ext (mul_inv_eq_one.mp hu'1).symm
    rw [e1, e2]
  have h3 := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_prod] at h3
  exact h3

end Fix

end CFSG.Quasithin
