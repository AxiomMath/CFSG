module

public import CFSG.Monster.Generated.TwoLocal
public import CFSG.Monster.VisQuot.Simple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Generated

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible

theorem generated_rational_group_finite_simple :
    Nontrivial Gmat ∧ IsSimpleGroup Gmat ∧ Finite Gmat :=
  generated_group_two_local_simplicity_reduction VisQuot.visible_quotient_simple.1
    visible_quotient_irreducible_action.1

end CFSG.Monster.Generated
