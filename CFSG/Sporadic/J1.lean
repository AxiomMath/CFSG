module

public import CFSG.Sporadic.J1.Simple

public section

namespace CFSG.Sporadic.J1

open CFSG.Blueprint

theorem isSimpleGroup_J1 : IsSimpleGroup NativeSporadic.J1 :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J nativeEquiv

theorem card_J1 : Nat.card NativeSporadic.J1 = 175560 := by
  rw [Nat.card_congr nativeEquiv.toEquiv, card_J]

theorem fam_j1_simplicity :
    Finite NativeSporadic.J1 ∧ Nontrivial NativeSporadic.J1 ∧
    IsSimpleGroup NativeSporadic.J1 :=
  ⟨Nat.finite_of_card_ne_zero (by rw [card_J1]; norm_num), isSimpleGroup_J1.toNontrivial,
    isSimpleGroup_J1⟩

end CFSG.Sporadic.J1
