module

public import CFSG.Quasithin.Recognition.RuTypeSL3

public section

namespace CFSG.Quasithin.RuType.SL3

open scoped MatrixGroups

@[expose] def IsRow0 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  A 0 0 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = 0 ∧ A 1 2 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 ∧ A 2 2 = 0

instance : DecidablePred IsRow0 := fun A =>
  inferInstanceAs (Decidable (A 0 0 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = 0 ∧ A 1 2 = 0 ∧ A 2 0 = 0 ∧
    A 2 1 = 0 ∧ A 2 2 = 0))

theorem fix_R0_iff : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
    ((∀ g ∈ R0, stAct g A = A) ↔ IsRow0 A) := by
  decide +kernel

theorem card_row0 : Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsRow0 A} = 4 := by
  decide +kernel

theorem row0_trace : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), IsRow0 A → A.trace = 0 := by
  decide +kernel

theorem row0_conj_inter : ∀ g : SL(3, ZMod 2), g ∉ Stab0 →
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), IsRow0 A → IsRow0 (stAct g⁻¹ A) → A = 0 := by
  decide +kernel

theorem exists_functional_basis : ∀ a : Fin 3 → ZMod 2, a ≠ 0 →
    ∃ h : SL(3, ZMod 2), ∀ y : Fin 3 → ZMod 2, a ⬝ᵥ natAct3 h y = y 2 := by
  decide +kernel

theorem P0_plane : ∀ g ∈ P0, ∀ y : Fin 3 → ZMod 2, y 2 = 0 → (natAct3 g y) 2 = 0 := by
  decide +kernel

end CFSG.Quasithin.RuType.SL3
