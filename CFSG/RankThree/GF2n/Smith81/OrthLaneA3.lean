module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Natural
public import CFSG.RankThree.GF2n.Smith81.OrthE1Step1
public import CFSG.RankThree.GF2n.Smith81.OrthE1NtCentral
public import CFSG.RankThree.GF2n.Smith81.OrthE1Small
public import CFSG.RankThree.GF2n.Smith81.OrthE1RtSplit
public import CFSG.RankThree.GF2n.Smith81.OrthE1NtLine
public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaC
public import CFSG.RankThree.GF2n.Smith81.OrthE1Ct
public import CFSG.RankThree.GF2n.Smith81.OrthE1CtStructure
public import CFSG.RankThree.GF2n.Smith81.OrthE1Fitting
public import CFSG.RankThree.GF2n.Smith81.OrthE1TheoremR
public import CFSG.RankThree.GF2n.Smith81.OrthE1B1
public import CFSG.RankThree.GF2n.Smith81.OrthE1B2
public import CFSG.RankThree.GF2n.Smith81.OrthE1B7a
public import CFSG.RankThree.GF2n.Smith81.OrthE1B7c
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFSmall
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
public import CFSG.RankThree.GF2n.Smith81.OrthE1KF3p
public import CFSG.RankThree.GF2n.Smith81.OrthE1KF11a
public import CFSG.RankThree.GF2n.Smith81.OrthE1Triple
public import CFSG.RankThree.GF2n.Smith81.OrthE1B7b
public import CFSG.RankThree.GF2n.Smith81.OrthE1KF10
public import CFSG.RankThree.GF2n.Smith81.OrthE1B6
public import CFSG.RankThree.GF2n.Smith81.OrthE1B8
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseA1
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylow
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseA3
public import CFSG.RankThree.GF2n.Smith81.OrthE1KF9
public import CFSG.RankThree.GF2n.Smith81.OrthLaneA2
public import CFSG.RankThree.GF2n.Smith81.Orth28Witness
public import CFSG.RankThree.GF2n.Smith81.Orth28DT
public import CFSG.RankThree.GF2n.Smith81.Orth28EpsFour
public import CFSG.RankThree.GF2n.Smith81.Orth28FourMinus
public import CFSG.RankThree.GF2n.Smith81.Orth212C4Root
public import CFSG.RankThree.GF2n.Smith81.Orth212C7
public import CFSG.RankThree.GF2n.Smith81.Orth28CaseIRoot
public import CFSG.RankThree.GF2n.Smith81.Orth28CaseIPBot
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB2
public import CFSG.RankThree.GF2n.Smith81.Lin212Rest
public import CFSG.RankThree.GF2n.Smith81.Lin26Normal
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseA2
public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleLevi
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime
public import CFSG.RankThree.GF2n.Smith81.Sec220Defs
public import CFSG.RankThree.GF2n.Smith81.Sec220Local
public import CFSG.RankThree.GF2n.Stroth80.Sec12Aniso
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVICoord
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stab

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem smith24Act_of_23 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) (hG : StrothGenByBStatement) (h23 : Smith23E1LgenStatement) :
    Smith24ActStatement :=
  smith24Act_of_four h34 h310 hG (smith24ActFour_of h23 (smith24ActE2Two_holds h34 h310 hNt hG))

theorem smith28Orth_of_remaining (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) (hG : StrothGenByBStatement) (h23 : Smith23E1LgenStatement)
    (hSim4 : OrthSimFourPlusStatement) (hR04 : OrthR0HypFourStatement)
    (hDT4 : OrthDTHypFourStatement) : Smith28OrthStatement := by
  have hT := orthTacit_of_noA2E1 hG orthNoA2E1Statement_holds
  have h24 := smith24Act_of_23 h34 h310 hNt hG h23
  have h25 := smith25Orth_of_inputs h34 hT
  have h52 := smith52Act_of h25 hT
  have hnc := orthNoCaseI_of_leaves (orthCaseIPBot_of_fourPlus h24 hT hSim4)
    (orthCaseIRoot_of h24 hT) (orth212C4Root_of h24 h52)
  exact smith28Orth_of_strong (orthR0_of_hypFour h24 hR04)
    (orth28Strong_of_eps (orthEps_of_25 h24 h25 hT) orthWitness_holds
      (orthDT_of_hypFour h24 h52 hT hDT4) hnc)

theorem smith212OrthCore_of_remaining (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) (hG : StrothGenByBStatement) (h23 : Smith23E1LgenStatement)
    (h28 : Smith28OrthStatement) (h5 : Orth212C5CondStatement) : Smith212OrthCoreStatement := by
  have hT := orthTacit_of_noA2E1 hG orthNoA2E1Statement_holds
  have h24 := smith24Act_of_23 h34 h310 hNt hG h23
  have h52 := smith52Act_of (smith25Orth_of_inputs h34 hT) hT
  have h4 := orth212C4Cond_of_root (orth212C4Root_of h24 h52) h28
  exact smith212OrthCore_of_cond h28 h4 h5 (orth212C7Cond_of_C4 h4 h28)

end CFSG.RankThree.GF2n.Smith81
