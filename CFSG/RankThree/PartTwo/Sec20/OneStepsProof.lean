module

public import CFSG.RankThree.PartTwo.Sec20.OneFrontierClean
public import CFSG.RankThree.PartTwo.Sec20.OneStepsProofV
public import CFSG.RankThree.PartTwo.Sec20.OneStepsProofL

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem item209One_of_step209L (h207 : Item207One) (h208 : Item208One) (hL : Step209L) :
    Item209One :=
  item209One_of_steps_clean h207 h208 step209V_proof hL

theorem item209One_of_step209L_parts (h207 : Item207One) (h208 : Item208One)
    (hN : Step209LNormal) (hC : Step209LCentral) : Item209One :=
  item209One_of_step209L h207 h208 (step209L_of hN hC)

end CFSG.RankThree.PartTwo.Sec20
