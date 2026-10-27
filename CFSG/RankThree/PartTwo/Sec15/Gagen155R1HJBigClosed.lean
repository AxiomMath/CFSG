module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJBig
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJBig156
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLeClosed
public import CFSG.RankThree.PartTwo.Sec15.Ronan153Big

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15


theorem res1J2Item156Big_holds
    (h152 : Item152BigR) (h153 : Ronan153Big.Item153BigR) :
    Res1J2Item156Big :=
  res1J2Item156Big_of Ronan148M.item148R_holds item134_holds Sec11.Close.closed_sec4Item4_8
    Sec4.Sporadic.rank3II_4_15 item142AllS14_holds item1411_1R_holds h152 h153
    (Ronan153Big.claim153ObsBigR_of Ronan148M.item148R_holds Ronan149.item149S14_holds h152)

theorem res1L112InPt_j2_big
    (h154 : Item154R) (h152 : Item152BigR)
    (h153 : Ronan153Big.Item153BigR) : Res1L112InPtBig Res1J2Pt Res1OpenType :=
  res1L112InPt_j2_big_of_j2K item134_holds Sec11.Close.closed_sec4Item4_8 Ronan148M.item148R_holds
    (item142R_of_wired item142AllS14_holds) (hjThetaS14_of_item135 item135_holds)
    (res1L112InPtJ2K_j2_holds h154) (res1J2Item156Big_holds h152 h153) res1J2X1_holds

theorem step155HostE0WRes1TypeFPtBig_j2
    (h154 : Item154R) (h152 : Item152BigR)
    (h153 : Ronan153Big.Item153BigR) : Step155HostE0WRes1TypeFPtBig Res1J2Pt Res1OpenType :=
  step155HostE0WRes1TypeFPtBig_of_le_of_in Ronan149.item149S14_holds
    (fun _ _ _ _ _ _ hPt => hPt.2) step155HostE0WRes1TypeFBarLe_hj_holds
    (res1L112InPt_j2_big h154 h152 h153)

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
