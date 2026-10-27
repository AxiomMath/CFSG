module

public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofRem187Q
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofHyp191
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18 CFSG.RankThree.PartTwo.Sec19

theorem rem187_of_item181
    (h4443 : Sec4.Item4_44_3)
    (h45 : Sec4.Item4_5) (h1811 : Item181_1) (h1812 : Item181_2) (hET : Item183ET) : Rem187 := by
  have h183One := item183One_of_item181 h45 h1811 h1812 hET
  have h1841 := rank3II_18_4_1_of_item183One h1812 h183One
    (claim184LcLe_of h1812 (Sec4.item4_44_3SL_of_item4_44_3 h4443))
  exact rem187_of_item4443 h4443 h1812 h1841 (item183K_of_item183One h183One)

theorem item2010_of_item181
    (h4443 : Sec4.Item4_44_3)
    (h45 : Sec4.Item4_5) (h1811 : Item181_1) (h1812 : Item181_2) (hET : Item183ET)
    (h201 : Sec20.Item201Contra1) : Item2010 :=
  rank3II_20_10_reduction h1811 (rem187_of_item181 h4443 h45 h1811 h1812 hET) h201

end CFSG.RankThree.PartTwo.Late
