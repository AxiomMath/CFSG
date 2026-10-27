module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.Quasithin.S146zX

theorem card_le_six_of_index_three {X : Type} [Group X] [IsSimpleGroup X] (A : Subgroup X)
    (hA : A.index = 3) : Nat.card X ≤ 6 := by
  have hAtop : A ≠ ⊤ := by
    rintro rfl
    simp at hA
  have hker : A.normalCore = ⊥ := by
    rcases A.normalCore_normal.eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ A.normalCore_le)) hAtop
  have hinj : Function.Injective (MulAction.toPermHom X (X ⧸ A)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    exact hker
  have hcard : Nat.card (X ⧸ A) = 3 := hA
  have hfin : Finite (X ⧸ A) := Nat.finite_of_card_ne_zero (by omega)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_perm, hcard] at hle
  exact hle

theorem not_index_three_of_card_sixty {X : Type} [Group X] [IsSimpleGroup X]
    (h : Nat.card X = 60) (A : Subgroup X) : A.index ≠ 3 := by
  intro hA
  have := card_le_six_of_index_three A hA
  omega

end CFSG.Quasithin.S146zX
