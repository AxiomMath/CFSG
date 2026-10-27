module

public import CFSG.Sporadic.Schreier.Co1SignedCover

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix CFSG.Blueprint

theorem ternary_code_signed_M12_cover :
    (∀ g ∈ Q, ∀ v ∈ T, (g : Matrix (Fin 12) (Fin 12) (ZMod 3)) *ᵥ v ∈ T) ∧
    (∀ c : Fin 12, (coordBij c : ℕ) = [0, 1, 2, 3, 4, 7, 11, 6, 5, 10, 9, 8].getD c.val 0) ∧
    ∃ π : Q →* Equiv.Perm (Fin 12),
      (∀ (g : Q) (i j : Fin 12),
        ((g : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) i j ≠ 0 ↔ i = π g j) ∧
      π.range = NativeSporadic.M12.map (MulAut.conj coordBij).toMonoidHom ∧
      (∀ g : Q, π g = 1 ↔ (g : GL (Fin 12) (ZMod 3)) = 1 ∨ (g : GL (Fin 12) (ZMod 3)) = -1) ∧
      (∀ g : Q, g ∈ Subgroup.center Q ↔
        (g : GL (Fin 12) (ZMod 3)) = 1 ∨ (g : GL (Fin 12) (ZMod 3)) = -1) ∧
      Nat.card Q = 190080 ∧
      (¬ ∃ s : π.range →* Q, ∀ x, π (s x) = x) ∧
      commutator Q = ⊤ :=
  ⟨Q_preserves_T, coordBij_apply, qPerm, qPerm_pattern, range_qPerm, qPerm_eq_one_iff,
    mem_center_Q_iff, card_Q, not_exists_section, commutator_Q⟩

end CFSG.Sporadic.Co1Schreier
