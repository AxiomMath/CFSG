module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import CFSG.RankThree.PartTwo.Sec15.Item15No135
public import CFSG.RankThree.PartTwo.Sec17.Item17MClaims
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof
import CFSG.RankThree.PartTwo.Sec17.Item1713

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17

section Item146

theorem item146S14_of (h142 : Concl142S14) (h143 : Concl143S14) : Item146S14 :=
  item146_forall_of_concl h142 h143

end Item146

theorem item145BotS14_of (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) : Item145BotS14 :=
  forall_exists_isHyperplane_lB_eq_bot h134 h48 h415

theorem item145BotS17_of (h : Item145BotS14) : Item145BotS17 :=
  fun G _ _ A c L _ hs => h G A c L hs.toSec14Std

theorem claim1411LocalR_of (h146 : Item146S14) (hbot : Item145BotS14)
    (hW : Claim1411NonsolvWR) (hX : Claim1411NonsolvXR) : Claim1411LocalR :=
  fun G _ _ A c L hR => claim1411Local_of_nonsolvable hR.toSec14Std
    (h146 G A c L hR.toSec14Std) (hbot G A c L hR.toSec14Std) (hW G A c L hR) (hX G A c L hR)

theorem item1411_1R_of (h : Claim1411LocalR) : Item1411_1R :=
  fun G _ _ A c L hR => rank3II_14_11_1_of hR.toSec14Std (h G A c L hR)

theorem item1411_1S17_of (h : Item1411_1R) : Item1411_1S17 :=
  fun G _ _ A c L _ hs => h G A c L hs.toSec15R

end CFSG.RankThree.PartTwo.Sec14

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17

theorem item152R_of
    (h44 : Sec4.Item4_4) (h148 : Item148R) (h1411 : Item1411_1R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hst : CFSG.RankThree.PartTwo.StellmacherKP) (hcomp : Step152CompR)
    (hexcl : Step152ExclR) (hconf : Step152ConfR) (hgen : KS152HJGen) (hend : Step152EndR) :
    Item152R :=
  fun G _ _ A c L hR => rank3II_15_2_of' hR.toSec14Std h44 (h148 G A c L hR) (h1411 G A c L hR)
    h134 h48 h415 hst (hcomp G A c L hR) (hexcl G A c L hR) (hconf G A c L hR) hgen
    (hend G A c L hR)

theorem item1514S17_of (h1515 : Step1515S17) (h1519 : Step1519S17) (h1521 : Step1521S17)
    (h1522 : Step1522S17) : Item1514S17 :=
  fun G _ _ A c L Y₀ hs => rank3II_15_14_of_steps (h1515 G A c L Y₀ hs) (h1519 G A c L Y₀ hs)
    (h1521 G A c L Y₀ hs) (h1522 G A c L Y₀ hs)

end CFSG.RankThree.PartTwo.Sec15

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16

theorem claim17MR_of
    (h163 : Item163R)
    (h152 : Item152R) : Claim17MR :=
  fun G _ _ A c L hR => claim17M_of_item163 hR (h163 G A c L hR) (h152 G A c L hR)

theorem item179S17_of (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17)
    (h146 : Item146S14) (h177 : Item177S17) : Item179S17 :=
  fun G _ _ A c L Y₀ hs => rank3II_17_9_of hs (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
    (h168 G A c L Y₀ hs) (h146 G A c L hs.toSec14Std) (h177 G A c L Y₀ hs)

theorem item1710S17_of (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17)
    (h179 : Item179S17) : Item1710S17 :=
  fun G _ _ A c L Y₀ hs => rank3II_17_10_of hs (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
    (h168 G A c L Y₀ hs) (h179 G A c L Y₀ hs)

theorem item1713S17_of (h1712 : Item1712S17) (h172 : Item172S17) : Item1713S17 :=
  fun G _ _ A c L Y₀ hs => rank3II_17_13_of hs.toSec14Std.isE27 (h1712 G A c L Y₀ hs)
    (h172 G A c L Y₀ hs)

theorem item1714S17_of (h1713 : Item1713S17) (h165 : Item165S17) : Item1714S17 :=
  fun G _ _ A c L Y₀ hs => rank3II_17_14_of ⟨Y₀, hs.mem_y0Star.prop⟩ (h1713 G A c L Y₀ hs)
    (h165 G A c L Y₀ hs)

theorem cardInfNineS17_of (h : ProdLBarS17) : CardInfNineS17 :=
  fun G _ _ A c L Y₀ hs => card_inf_eq_nine_of_prod hs (h G A c L Y₀ hs)

end CFSG.RankThree.PartTwo.Sec17
