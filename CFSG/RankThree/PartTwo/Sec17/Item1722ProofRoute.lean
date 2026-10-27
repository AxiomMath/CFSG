module

public import CFSG.RankThree.PartTwo.Sec17.Item1722Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec16

theorem item1722_of (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17)
    (hX : Claim1722X) (hT : Claim1722T) (h1720 : Claim1720) : Item1722 :=
  fun G _ _ A c L Y₀ Y₁ S p P h =>
    rank3II_17_22_of h (h166 G A c L Y₀ h.toSec17Std) (hbot G A c L Y₀ h.toSec17Std)
      (h168 G A c L Y₀ h.toSec17Std) (hX G A c L Y₀ Y₁ S p P h) (hT G A c L Y₀ Y₁ S p P h)
      (h1720 G A c L Y₀ Y₁ S p P h)

end CFSG.RankThree.PartTwo.Sec17
