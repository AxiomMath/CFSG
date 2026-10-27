module

public import CFSG.Quasithin.MS93.S511SStep2
public import CFSG.Quasithin.MS93.S510S11

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S511S

theorem s511Core_of (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h53 : S53) (h54 : S54)
    (h56f : S5.S56f) (hZ : S5Q2.Q2EvenZ) (h59 : S5B.S59) : S5B.S511Core := by
  intro G _ _ M T L h hmin hb k F _ _ a hd h56all
  obtain ⟨c, hc⟩ := h.critDist_even
  rcases Nat.lt_or_ge 6 (critDist (puAmalgam h.le)) with hb6 | hb6
  · exact false_of_gt6 h32 hX2 h52 h53 h54 h56f hZ h59 h hmin hd hb6 h56all
  · exact false_of_b6 h32 hX2 h52 h53 h54 h56f hZ h59 h hmin hd (by omega) h56all

end S511S

end CFSG.Quasithin.MS93
