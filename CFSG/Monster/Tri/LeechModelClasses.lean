module

public import CFSG.Monster.Existence.InvolutionClasses
public import CFSG.Monster.Tri.LeechLongMonster

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open SimpleGraph CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups

theorem xGmat_eq_xmatG : xGmat = xmatG := Subtype.ext rfl

theorem tGmat_eq_tStarG : tGmat = tStarG := Subtype.ext rfl

variable {a : Gmat}

end CFSG.Monster.Tri.Leech
