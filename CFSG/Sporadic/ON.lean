module

public import CFSG.Sporadic.ON.Simple

public section

namespace CFSG.Sporadic.ON

open CFSG.Blueprint

theorem card_ON :
    Nat.card NativeSporadic.ON = 460815505920 := card_ON_eq

theorem fam_on_simplicity :
    Finite NativeSporadic.ON ∧ Nontrivial NativeSporadic.ON ∧
    IsSimpleGroup NativeSporadic.ON :=
  ⟨Nat.finite_of_card_ne_zero (by rw [card_ON]; norm_num), isSimpleGroup_ON.toNontrivial,
    isSimpleGroup_ON⟩

end CFSG.Sporadic.ON
