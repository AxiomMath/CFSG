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
public import CFSG.RankThree.GF2n.Smith81.OrthE1Triple2
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAb
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.RankThree.GF2n.Smith81.LinOddBasic
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Smith81.LinStmt
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseA2
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime
public import CFSG.RankThree.GF2n.Smith81.Sec220Defs
public import CFSG.RankThree.GF2n.Smith81.Sec220Local

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem smith23E1Lgen_of_remaining2 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) (h44 : Stroth44Statement) (hG : StrothGenByBStatement)
    (hW : CFSG.Walter.WalterModelsForm) (hWL : KFacts.WalterListLargeSylowStatement)
    (hA2 : CaseA2Statement) (hKF7 : ListNoPerfectOutStatement) :
    Smith23E1LgenStatement := by
  have hN := e1Natural_of_nt h34 h310 hNt
  have hS1 := step1_of h34 hN parabolic_holds
  have hC := ntCentral_of hNt hN hS1 parabolic_holds
  have hT := tMemNt_of hC hN omega4Basic_holds
  have hSplit := rtSplit_of h34 hNt hN hC hT omega4Basic_holds
  have hNK := e1NaturalK_of hN hSplit hNt natIrred_holds
  have hLine := ntLine_of hNt hNK hS1 hC parabolic_holds natIrred_holds
  have hTI := ntTI_of hLine
  have hLC := lemmaC_of parabolic_holds natIrred_holds
  have hCt := ctStructure_of hNK hSplit ctNormalizes_of hLine hLC normalizerOmega_holds
  have hF := m1FittingTrivial_of h44
  have hR := theoremR_of hLC sl2Root_holds hSplit hNK hLine hCt hF
  have hB1 := b1_of hLine hTI hSplit hNK omegaLine_holds
  have hB2 := b2_of hCt hSplit hTI
  have hTri := triple_of_free h1Tensor_holds sp4Involution_holds hNK hLine hCt hSplit hLC hS1
  have hD := caseBData_of_steps hB1 hB2 hTri
  have hB6 := b6_of hD hCt hSplit (ntConjLB_of hSplit) hB1 hB2 hTri
  have hB := caseBFalse_of_steps hD hB6 (b7a_of hB6) (b7b_of hB1 hB6 hTri hSplit) b7c_of
    (b8_of hW hWL hF hSplit hB6 (b7a_of hB6))
  have hA1 := caseA1_of hNK hCt hSplit hLine hTI dicksonNat_holds dicksonSpace_holds
  have hAb := CaseASylowAb.caseASylowAbelian_of hA2 ctNormalizes_of hSplit hLine hNK
    natIrred_holds dicksonNat_holds normalizerOmega_holds omega4Basic_holds
  have hA3 := caseA3_of hA2 hKF7 hCt hSplit (caseASylow_of hA1 hLine) hAb hW hWL hC
    (ntElemAbelian_of hLine)
  have hP1 := xNormal_of (ntConjLB_of hSplit) hB hA3 (caseA4_of hCt hSplit hT)
  exact smith23E1Lgen_of_steps orthNoA2E1Statement_holds hG hSplit hR hP1

end CFSG.RankThree.GF2n.Smith81.Smith23E1
