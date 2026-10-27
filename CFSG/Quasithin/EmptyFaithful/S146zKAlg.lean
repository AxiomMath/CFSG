module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

section Alg

variable {G : Type*} [Group G]

@[expose] def zCommModSub (U Z : Subgroup G) (κ : G) (hUZ : ∀ y ∈ U, ∀ z ∈ Z, y * z = z * y) :
    Subgroup G where
  carrier := {y | y ∈ U ∧ κ * y * κ⁻¹ * y⁻¹ ∈ Z}
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
    refine ⟨U.mul_mem hy₁ hy₂, ?_⟩
    have e : κ * (y₁ * y₂) * κ⁻¹ * (y₁ * y₂)⁻¹ =
        (κ * y₁ * κ⁻¹ * y₁⁻¹) * (y₁ * (κ * y₂ * κ⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
    rw [e]
    refine Z.mul_mem h₁ ?_
    have h3 := hUZ y₁ hy₁ _ h₂
    have e2 : y₁ * (κ * y₂ * κ⁻¹ * y₂⁻¹) * y₁⁻¹ = κ * y₂ * κ⁻¹ * y₂⁻¹ := by
      rw [h3]
      group
    rw [e2]
    exact h₂
  one_mem' := ⟨U.one_mem, by simp⟩
  inv_mem' := by
    rintro y ⟨hy, h⟩
    refine ⟨U.inv_mem hy, ?_⟩
    have e : κ * y⁻¹ * κ⁻¹ * y⁻¹⁻¹ = y⁻¹ * (κ * y * κ⁻¹ * y⁻¹)⁻¹ * y := by group
    rw [e]
    have h3 := hUZ y⁻¹ (U.inv_mem hy) _ (Z.inv_mem h)
    rw [h3]
    simpa using Z.inv_mem h

theorem forall_commutator_mem_of_gens {U K Z : Subgroup G} {c κ : G}
    (hUZ : ∀ y ∈ U, ∀ z ∈ Z, y * z = z * y) (hKU : K ≤ U) (hc : c ∈ U)
    (hUsup : U ≤ K ⊔ Subgroup.zpowers c) (hK : ∀ y ∈ K, κ * y * κ⁻¹ * y⁻¹ ∈ Z)
    (hcZ : κ * c * κ⁻¹ * c⁻¹ ∈ Z) : ∀ y ∈ U, κ * y * κ⁻¹ * y⁻¹ ∈ Z := by
  have hle : K ⊔ Subgroup.zpowers c ≤ zCommModSub U Z κ hUZ :=
    sup_le (fun y hy => ⟨hKU hy, hK y hy⟩) (Subgroup.zpowers_le.mpr ⟨hc, hcZ⟩)
  intro y hy
  exact (hle (hUsup hy)).2

end Alg

end CFSG.Quasithin
