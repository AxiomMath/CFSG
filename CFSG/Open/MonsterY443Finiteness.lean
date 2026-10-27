module

public import CFSG.Milestones.FAM_M_finiteness
public import CFSG.Milestones.FAM_M_simplicity

public section

universe u v w

namespace CFSG.Open.Open

open CFSG.Open in
theorem monster_y443_derived_card : Nat.card MonsterY443Derived = monsterOrder :=
  _root_.CFSG.Milestones.fam_m_finiteness

end CFSG.Open.Open

namespace CFSG.Open.Open

open CFSG.Open in
theorem monster_y443_derived_simple : IsSimpleGroup MonsterY443Derived :=
  _root_.CFSG.Milestones.fam_m_simplicity

end CFSG.Open.Open
