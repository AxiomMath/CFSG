
module


public import CFSG.Sporadic.Ly.Primitive

public section

namespace CFSG.Sporadic.Ly

open CFSG.Blueprint

theorem fam_ly_simplicity :
    Finite NativeSporadic.Ly ∧ Nontrivial NativeSporadic.Ly ∧
    IsSimpleGroup NativeSporadic.Ly := by
  have h : IsSimpleGroup NativeSporadic.Ly := isSimpleGroup_Ly
  exact ⟨Nat.finite_of_card_ne_zero (by rw [card_Ly']; norm_num), h.toNontrivial, h⟩

theorem card_Ly :
    Nat.card NativeSporadic.Ly = 51765179004000000 := card_Ly'

end CFSG.Sporadic.Ly
