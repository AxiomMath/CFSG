module

public import CFSG.Sporadic.J4

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Blueprint

theorem FAM_J4_certified_simplicity :
    Nontrivial NativeSporadic.J4 ∧ IsSimpleGroup NativeSporadic.J4 ∧
      Nat.card NativeSporadic.J4 = 86775571046077562880 :=
  ⟨CFSG.Sporadic.J4.fam_j4_simplicity.2.1, CFSG.Sporadic.J4.fam_j4_simplicity.2.2,
    CFSG.Sporadic.J4.card_J4⟩

end CFSG.Sporadic.J4Schreier
