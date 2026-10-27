module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Finite.Card

namespace CFSG
end CFSG
open CFSG

/-! # Cardinality of a subgroup join under a normalizer hypothesis -/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- If `B` normalizes `A` and they are disjoint, their join has cardinality
`|A| * |B|`. -/
public theorem card_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type u} [Group G]
    (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↑(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

end CFSG.GorensteinWalter
