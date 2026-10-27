module

public import CFSG.RankThree.PartTwo.Sec17.Item1721Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec16

theorem item1721_of (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17)
    (h146 : Item146S14) (h9 : CardInfNineS17) (h1719 : Item1719) (h1720 : Claim1720)
    (hT : Claim1721T) (hS : Claim1721S) : Item1721 :=
  fun G _ _ A c L Y₀ Y₁ S p P h =>
    rank3II_17_21_of h (h166 G A c L Y₀ h.toSec17Std) (hbot G A c L Y₀ h.toSec17Std)
      (h168 G A c L Y₀ h.toSec17Std) (h146 G A c L h.toSec14Std) (h9 G A c L Y₀ h.toSec17Std)
      (h1719 G A c L Y₀ Y₁ S p P h) (rank3II_17_20_le_of h h1720)
      (hT G A c L Y₀ Y₁ S p P h) (hS G A c L Y₀ Y₁ S p P h)

end CFSG.RankThree.PartTwo.Sec17
