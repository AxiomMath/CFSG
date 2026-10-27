module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Order
public import CFSG.RankThree.PartTwo.Census.Sporadic.Cubic
public import CFSG.RankThree.PartTwo.Census.Sporadic.J4
public import CFSG.RankThree.PartTwo.Census.Sporadic.Coxeter
public import CFSG.RankThree.PartTwo.Census.Sporadic.J3
public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22
public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi23
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1
public import CFSG.RankThree.PartTwo.Census.Sporadic.McL
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co3
public import CFSG.RankThree.PartTwo.Census.Sporadic.ON
public import CFSG.RankThree.PartTwo.Census.Sporadic.Suz
public import CFSG.RankThree.PartTwo.Census.Sporadic.HN
public import CFSG.RankThree.PartTwo.Census.Sporadic.Ly
public import CFSG.RankThree.PartTwo.Census.Sporadic.B

public section

namespace CFSG.RankThree.PartTwo.Census

theorem item433Case_sporadic (s : TauCeti.SporadicName) : Item433Case (.sporadic s) := by
  cases s with
  | M11 => exact excluded433_M11.item433Case
  | M12 => exact excluded433_M12.item433Case
  | M22 => exact excluded433_M22.item433Case
  | M23 => exact excluded433_M23.item433Case
  | M24 => exact excluded433_M24.item433Case
  | J1 => exact excluded433_J1.item433Case
  | J2 => exact excluded433_J2.item433Case
  | J3 => exact excluded433_J3.item433Case
  | J4 => exact excluded433_J4.item433Case
  | HS => exact excluded433_HS.item433Case
  | McL => exact excluded433_McL.item433Case
  | He => exact excluded433_He.item433Case
  | Ru => exact excluded433_Ru.item433Case
  | Suz => exact excluded433_Suz.item433Case
  | ONan => exact excluded433_ON.item433Case
  | Co1 => exact excluded433_Co1.item433Case
  | Co2 => exact item433Case_Co2
  | Co3 => exact excluded433_Co3.item433Case
  | Fi22 => exact excluded433_Fi22.item433Case
  | Fi23 => exact excluded433_Fi23.item433Case
  | Fi24Prime => exact excluded433_Fi24Prime.item433Case
  | HN => exact excluded433_HN.item433Case
  | Ly => exact excluded433_Ly.item433Case
  | Th => exact item433Case_Th
  | B => exact excluded433_B.item433Case
  | M => exact excluded433_M.item433Case

end CFSG.RankThree.PartTwo.Census
