module

public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly (IsComponentOf)

@[expose] def ggFixSubgroup {C : Type} [Group C] (α : MulAut C) : Subgroup C where
  carrier := {g | α g = g}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

@[expose] def GGOutTwoPartLeTwo (C : Type) [Group C] : Prop :=
  ∀ S : Subgroup (MulAut C), IsPGroup 2 S →
    ((MulAut.conj : C →* MulAut C).range.subgroupOf S).index ≤ 2

@[expose] def GGGraphInvInputModel (C : Type) [Group C] : Prop :=
  ∀ (p : ℕ) (b : C) (α : MulAut C), p.Prime → p ≠ 2 → b ≠ 1 → b ^ p = 1 →
    α * α = 1 → (∀ c : C, α ≠ MulAut.conj c) → α b = b →
    (∃ L₁ : Subgroup C, IsComponentOf L₁ (Subgroup.centralizer {b})) →
    (∀ g ∈ Subgroup.centralizer {b}, α g = g) →
    GGOutTwoPartLeTwo C ∧
    (∀ N : Subgroup C, N ≤ ggFixSubgroup α → IsPGroup 2 N →
        (∀ y ∈ N, ∀ z ∈ ggFixSubgroup α, z * y * z⁻¹ ∈ N) → N = ⊥) ∧
    ¬ IsPGroup 2 ↥(ggFixSubgroup α) ∧
    Subgroup.centralizer ((ggFixSubgroup α : Subgroup C) : Set C) = ⊥

@[expose] def GGGraphInvFixClauses {C : Type} [Group C] (α : MulAut C) : Prop :=
  (∀ N : Subgroup C, N ≤ ggFixSubgroup α → IsPGroup 2 N →
      (∀ y ∈ N, ∀ z ∈ ggFixSubgroup α, z * y * z⁻¹ ∈ N) → N = ⊥) ∧
  ¬ IsPGroup 2 ↥(ggFixSubgroup α) ∧
  Subgroup.centralizer ((ggFixSubgroup α : Subgroup C) : Set C) = ⊥

end CFSG.StandardType
