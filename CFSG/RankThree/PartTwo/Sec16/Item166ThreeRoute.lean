module

public import CFSG.RankThree.PartTwo.Sec16.Item166ThreeMain
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec16.Wales166From1444
public import CFSG.RankThree.PartTwo.Sec16.Item166Res4Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank
  CFSG.GH74.GLS


theorem step166OmegaThreeOther_of (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS17) (h142 : Concl142R) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (h149 : Item149S14) (hRead : Y4CoreReadR)
    (hMem : Y4CoreMemR) (h152 : Item152R) (h155 : Item155R) (h148 : Item148R) :
    Step166OmegaThreeOther := by
  intro G _ _ A c L Y₀ h hL hJ
  exact Proof166Three.omega166Three_of_ne h
    (step166Gen_of_1444 h146 h1444 hbot h142 G A c L Y₀ h)
    (step166NoSz_of_items h1514 hMeets G A c L Y₀ h)
    (h146 G A c L h.toSec14Std)
    (h149 G A c L h.toSec14Std)
    (claim17Q0_of h1444 h146 hbot h1514 hMeets G A c L Y₀ h)
    (Proof166Three.omegaNe166_of_omg h
      (step1610Y4Star_of_core_s17 hRead hMem hbot h)
      (h152 G A c L h.toSec15R)
      (h155 G A c L h.toSec15R)
      (omg166Sz_of_omg166 (step166OmgOther_of h148 hbot h1514 hMeets G A c L Y₀ h hL hJ)))

theorem item166S17_of_1444_six (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS17) (h142 : Concl142R) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (h165 : Item165S17) (hRead : Y4CoreReadR)
    (hMem : Y4CoreMemR) (h152 : Item152R) (h155 : Item155R) (h148 : Item148R)
    (hA5Ctr : Step166CtrA5HJ) (h149 : Item149S14) : Item166S17 :=
  item166S17_of_1444_five h146 h1444 hbot h142 h1514 hMeets h165 hRead hMem h152 h155 h148 hA5Ctr
    (step166OmegaThreeOther_of h146 h1444 hbot h142 h1514 hMeets h149 hRead hMem h152 h155 h148)

end CFSG.RankThree.PartTwo.Sec16
