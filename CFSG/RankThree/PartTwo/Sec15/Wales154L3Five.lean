module

public import CFSG.RankThree.PartTwo.Sec15.Wales154L3Two
public import CFSG.RankThree.PartTwo.Sec15.Gagen1511Holds
import CFSG.RankThree.PartTwo.Sec15.Wales154KL3a
import CFSG.RankThree.PartTwo.Sec15.Wales154KL3c

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Five


theorem item154L3Five_of_items (h158 : Item158Y0R) (hset : Item13SetupAt) (h133 : Item133)
    (h159 : Item159R) (h1510 : Item1510R) (hBr : Sec16.Step169TwoBridge) (h134 : Item134)
    (h48 : Sec4.Item4_8) : Item154L3Five := by
  intro G _ _ A c L hR _ Y hY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC5 _ _
  exact (not_case148Five_of_sec15R h158 hset h133 h159 h1510 hBr h134 h48 hR hY hC5).elim

end Five

theorem item154ProperR_of_route
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) (hbot : Item145BotS14)
    (h142 : Item142R) (h158 : Item158Y0R)
    (hset : Item13SetupAt) (h133 : Item133) (h159 : Item159R) (h1510 : Item1510R)
    (hBr : Sec16.Step169TwoBridge) : Item154ProperR :=
  item154ProperR_of_five h148 h134 h48 hbot h142 kl3a_holds kl3c_holds
    (item154L3Five_of_items h158 hset h133 h159 h1510 hBr h134 h48)

end CFSG.RankThree.PartTwo.Sec15.Wales154
