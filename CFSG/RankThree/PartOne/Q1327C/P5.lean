module

public import CFSG.RankThree.PartOne.Q1327C.P5List
public import CFSG.RankThree.PartOne.SPOR.I613Even

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143

theorem kf1327P5_holds :
    Q1327.KF1327P5 :=
  fun G _ _ X A₀ F hb hlist hN =>
    evenListBridge_of_exceptional SPOR.evenExceptionalBridge_holds _
      (kf1327P5List_holds G X A₀ F hb hlist hN)

end CFSG.RankThree.PartOne.Q1327C
