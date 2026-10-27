module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLe
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJClosed
public import CFSG.RankThree.PartTwo.Sec14.Item1411_3RHolds
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

theorem res1L112InPtJ2K_j2_holds
    (h154 : Item154R) : Res1L112InPtJ2K Res1J2Pt Res1OpenType :=
  res1L112InPtJ2K_j2_of j2AutFixNine_holds j2HasE25_holds Sec4.Sporadic.rank3II_4_15 item134_holds
    Sec11.Close.closed_sec4Item4_8 Ronan148M.item148R_holds (item142R_of_wired item142AllS14_holds)
    Ronan148M.concl142S14_holds (hjThetaS14_of_item135 item135_holds)
    (step142LowerGenHJ_of_131 rank3II_13_1_holds) h154

theorem res1L112InPt_j2
    (h154 : Item154R) (h156 : Res1J2Item156) (hX1 : Res1J2X1) :
    Sylow155R1.Res1L112InPt Res1J2Pt Res1OpenType :=
  res1L112InPt_j2_of_j2K item134_holds Sec11.Close.closed_sec4Item4_8 Ronan148M.item148R_holds
    (item142R_of_wired item142AllS14_holds) (hjThetaS14_of_item135 item135_holds)
    (res1L112InPtJ2K_j2_holds h154) h156 hX1

theorem step155HostE0WRes1TypeFPt_j2
    (h154 : Item154R) (h156 : Res1J2Item156) (hX1 : Res1J2X1) :
    Step155HostE0WRes1TypeFPt Res1J2Pt Res1OpenType :=
  Sylow155R1.step155HostE0WRes1TypeFPt_of_le_of_in Ronan149.item149S14_holds
    (fun _ _ _ _ _ _ hPt => hPt.2) step155HostE0WRes1TypeFBarLe_hj_holds
    (res1L112InPt_j2 h154 h156 hX1)

theorem res1J2X1_holds
    : Res1J2X1 :=
  Gagen155R1HJX1.res1J2X1_of Ronan148M.item143QS14_holds Sec4.rank3II_4_5
    Sec11.Close.closed_sec4Item4_8 item134_holds

theorem step155HostE0WRes1TypeFPt_j2_of_156
    (h154 : Item154R) (h156 : Res1J2Item156) :
    Step155HostE0WRes1TypeFPt Res1J2Pt Res1OpenType :=
  step155HostE0WRes1TypeFPt_j2 h154 h156 res1J2X1_holds

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
