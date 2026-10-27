module

public import CFSG.RankThree.GF2n.Stroth80.Sec97FiveDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X Y : Subgroup G} {hc : Ctx M Q Z B} {t nn r g : G}

namespace HS9

theorem planeST_le_Vt (h13 : Sec97K13 hc t X Y r nn g) :
    planeST M Q Z B X nn g ≤ Vt M (LB M Q B) B Z nn := by
  rw [← h13.sup_eq]
  exact le_sup_right

theorem pointT_le_Vt (h13 : Sec97K13 hc t X Y r nn g) :
    pointT hc X Y nn g ≤ Vt M (LB M Q B) B Z nn :=
  inf_le_left.trans (planeST_le_Vt h13)

end HS9

end CFSG.RankThree.GF2n.Stroth80
