module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec14

theorem item148R_of_item148S14 (h148 : Item148S14) : Item148R :=
  fun G _ _ A c L h => h148 G A c L h.toSec14Std

end CFSG.RankThree.PartTwo.Sec14
