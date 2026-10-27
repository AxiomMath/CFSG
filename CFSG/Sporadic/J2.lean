module

public import CFSG.Sporadic.J2.Simple

public section

namespace CFSG.Sporadic.J2

open CFSG.Blueprint

theorem isSimpleGroup_J2 : IsSimpleGroup NativeSporadic.J2 :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J nativeEquiv

theorem card_J2 : Nat.card NativeSporadic.J2 = 604800 := by
  rw [Nat.card_congr nativeEquiv.toEquiv, card_J]

theorem fam_j2_simplicity :
    Finite NativeSporadic.J2 ∧ Nontrivial NativeSporadic.J2 ∧
    IsSimpleGroup NativeSporadic.J2 :=
  ⟨Nat.finite_of_card_ne_zero (by rw [card_J2]; norm_num), isSimpleGroup_J2.toNontrivial,
    isSimpleGroup_J2⟩

end CFSG.Sporadic.J2
