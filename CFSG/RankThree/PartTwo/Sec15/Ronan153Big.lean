module

public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigTypes
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigTwin
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigChar

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan153Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

theorem claim153ObsBigR_of
    (h148 : Item148R) (h149 : Sec16.Item149S14) (h152 : Item152BigR) : Claim153ObsBigR :=
  fun G _ _ A c L hR Y hY hYb => obsAt_of_big h149 hR (h152 G A c L hR) hY hYb
    (twinTypesAt_of_big h148 h149 hR (h152 G A c L hR) hY hYb)

section Wiring


theorem item153BigR_of
    (h316 : Sec19.Item316) (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h134 : Item134) (h135 : Item135) (h137 : Item137) (h142 : Item142AllS14)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h142c : Sec14.Concl142S14)
    (h143 : Sec14.Concl143S14) (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14)
    (hbot : Sec14.Item145BotS14) (h148HJ : Sec14.Item148HJS14) (h152 : Item152BigR) :
    Item153BigR := by
  intro G _ _ A c L hR Y hY hYb
  have h := hR.toSec14Std
  have hb := h152 G A c L hR
  have htw : TwinAt A Y := twinAt_of_big h148 h149 hR hb hY hYb
  have hobs : ObsAt A Y :=
    obsAt_of_big h149 hR hb hY hYb (twinTypesAt_of_big h148 h149 hR hb hY hYb)
  exact item153At_of_twinAt h (h149 G A c L h) hY htw
    (charAt_of h316 h149 h148 h134 h135 h137 h142 h48 h415 h142c h143 h146 h1444 hbot h148HJ
      hR hY htw hobs)

end Wiring

end CFSG.RankThree.PartTwo.Sec15.Ronan153Big
