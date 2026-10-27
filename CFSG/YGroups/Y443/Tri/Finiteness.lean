module

public import CFSG.YGroups.Y443.Tri.Final

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Open CFSG.Monster CFSG.Monster.Generated

theorem natCard_Gmat_eq_monsterOrder :
    Nat.card Gmat = monsterOrder := by
  rw [CFSG.Monster.AxisCount.HS.natCard_Gmat, CFSG.Monster.AxisCount.Baby.natCard_Cgen,
    CFSG.Monster.AxisCount.natCard_Jstar]
  norm_num [monsterOrder]

theorem fam_m_finiteness_of_ivanov
    (h : Y443IvanovInputs) :
    Nat.card MonsterY443Derived = monsterOrder := by
  rw [Nat.card_congr h.equiv.toEquiv, natCard_Gmat_eq_monsterOrder]

end CFSG.YGroups.Y443
