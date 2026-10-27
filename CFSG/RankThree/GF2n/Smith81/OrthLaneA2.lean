module

public import CFSG.RankThree.GF2n.Smith81.OrthE2PlusTwoRoot
public import CFSG.RankThree.GF2n.Smith81.OrthE1NotVI
public import CFSG.RankThree.GF2n.Smith81.OrthNoA2E1
public import CFSG.RankThree.GF2n.Smith81.OrthLaneA

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80


theorem orthNoA2E1Statement_holds : OrthNoA2E1Statement :=
  fun _ _ _ _ _ _ _ _ hc ht hE =>
    noA2All_of_caseE1_of_not_caseVI hc ht hE (not_caseVI_of_caseE1 hc ht hE)

theorem smith24ActE2Two_holds (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) (hG : StrothGenByBStatement) : Smith24ActE2TwoStatement :=
  smith24ActE2Two_of h34 h310 hG (smith24ActE2PlusTwo_holds h34 h310 hNt hG)

theorem smithLaneOrth_of_remaining2 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) (hG : StrothGenByBStatement) (hTim : TimmesfeldOutcomeStatement)
    (h217 : Smith217Statement) (h28 : Smith28OrthStatement) (h212 : Smith212OrthCoreStatement)
    (h213 : Smith213OrthStatement) (h23 : Smith23E1LgenStatement)
    (hInsp : Smith219OrthInspectionStatement) : LaneOrthStep :=
  smithLaneOrth_of_remaining h34 h310 hG hTim h217 h28 h212 h213 h23
    (smith24ActE2Two_holds h34 h310 hNt hG) orthNoA2E1Statement_holds hInsp

end CFSG.RankThree.GF2n.Smith81
