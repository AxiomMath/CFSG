module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG

namespace FiveTransitive.SimpleIndexBound

theorem card_le_factorial_index
    (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) (hH : H ≠ ⊤) :
    Nat.card G ≤ H.index.factorial := by
  classical
  have hcore : H.normalCore = ⊥ := by
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hH (top_le_iff.mp (h ▸ H.normalCore_le))).elim
  let f := MulAction.toPermHom G (G ⧸ H)
  have hker : f.ker = ⊥ := H.normalCore_eq_ker.symm.trans hcore
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_perm, ← H.index_eq_card] at hcard
  exact hcard

end FiveTransitive.SimpleIndexBound

end CFSG
