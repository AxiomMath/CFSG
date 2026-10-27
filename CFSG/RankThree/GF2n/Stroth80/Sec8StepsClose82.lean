module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec8Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem stroth82_of_81a (hA : Sec8AExistsStatement) (h81 : Stroth81Statement)
    (hF : Close82FalseStatement) : Stroth82Statement := by
  intro G _ _ M Q Z B hc n t hs
  by_contra ha
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hb := (h81 G M Q Z B hc n t hs r hr).resolve_left ha
  exact hF G M Q Z B hc n t r ⟨hs, hr, ha, hb⟩

end CFSG.RankThree.GF2n.Stroth80
