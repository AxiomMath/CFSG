module

public import CFSG.Quasithin.MS93.S59RCore
public import CFSG.Quasithin.MS93.S59

public section

namespace CFSG.Quasithin.MS93.S59R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem open_of (h32 : S32) (hX2 : S33.S33X52) (h53 : S53) (h55 : S55) (h56 : S56)
    (h58 : S5B.S58) : S59.Open := by
  intro G _ _ M T L h hmin hb k F _ _ a hd hk α' hc hαβ' hP hnc
  exfalso
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨ξ, hξ, hξα⟩ := S59.exists_crit_gamma h58 h hmin hb' hd hc
  exact case1_false h32 hX2 h53 h55 h56 h hmin hb hd hk hc hαβ' hξ hξα hP hnc

end CFSG.Quasithin.MS93.S59R
