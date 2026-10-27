module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLeavesGJ
public import CFSG.RankThree.GF2n.Stroth80.Sec7OutSolvableAlpha
public import CFSG.RankThree.GF2n.Stroth80.Sec7TwoRankSmall
public import CFSG.RankThree.GF2n.Tim77.Cor2Sec53
public import CFSG.RankThree.GF2n.Tim77.Sec53F
public import CFSG.RankThree.GF2n.Stroth80.Sec108Spread
public import CFSG.RankThree.GF2n.Tim81.GF2nTypeRemaining86

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section Certs

theorem sec7Tail_of_two
    (hCor2 : Tim77Cor2Statement) (hTim : Tim81StrothUnRootStatement) :
    Stroth78Statement ∧ Stroth79Statement ∧ Stroth716TypeStatement ∧ Stroth717Statement :=
  sec7Tail_of_leavesGJ
    { cor2 := hCor2
      outSolvAlpha := outSolvableAlpha_of_rankTwo outSolvableRankTwo_holds
      corB := CFSG.CGT.Timmesfeld75.corollaryBStmt_of_theoremAStmt
        CFSG.CGT.Timmesfeld75.theoremAStmt_holds
      outSolv := outSolvableList_holds
      twoRank := twoRankSporadicAlt_holds
      outSolvU6 := outSolvableUnitarySix_holds
      tim81unRoot := hTim }

theorem stroth716TypeStatement_of_two
    (hCor2 : Tim77Cor2Statement)
    (hTim : Tim81StrothUnRootStatement) : Stroth716TypeStatement :=
  (sec7Tail_of_two hCor2 hTim).2.2.1

theorem stroth717Statement_of_two
    (hCor2 : Tim77Cor2Statement)
    (hTim : Tim81StrothUnRootStatement) : Stroth717Statement :=
  (sec7Tail_of_two hCor2 hTim).2.2.2

theorem tim77Cor2_holds
    : Tim77Cor2Statement :=
  Tim77.tim77Cor2_of_sec53 (Tim77.sec53_of_four CFSG.RankThree.GF2n.Tim77.sec53_four_holds)

theorem stroth713Statement_unconditional
    : Stroth713Statement := by
  have h34 : Stroth34Statement := stroth34Statement_unconditional
  have h310 : Stroth310Statement := stroth310Statement_unconditional
  have h311a : Stroth311aStatement := stroth311aStatement_unconditional
  have h51 : Stroth51Statement := stroth51Statement_unconditional
  have h310chi : Stroth310ChiStatement := stroth310Chi_of_34 h34
  have h310root : Stroth310RootStatement := stroth310Root_of_34 h34
  have aEx : Sec7AExistsStatement := sec7AExistsStatement_unconditional
  have aEx8 : Sec8AExistsStatement := sec8AExistsStatement_unconditional
  have h52a : Stroth52aStatement := stroth52aStatement_holds
  have h52b : Stroth52bStatement := stroth52bStatement_holds
  have h56 : Stroth56NatStatement := stroth56Nat_of_34 h34
  have hpts : Sec5NatPointsOmegaStatement := sec5NatPointsOmega_of h34 h310root
  have hptsSp : Sec5NatPointsSpStatement := sec5NatPointsSp_of h34 h310root
  have centre : Sec7CentreMpStatement := sec7CentreMp_of_inputs h51 h52a aEx
  have zt : Sec7ZtStatement :=
    sec7Zt_of_inputs h34 h310 h51 h52a aEx aEx8 h56 hpts hptsSp
  have cv : Sec7CVStatement := sec7CV_of_inputs h34 h310root aEx h52b
  have conjOm4 : Sec7ConjOm4Statement := sec7ConjOm4_of_inputs h34 aEx hpts zt
  have zcard : Sec7ZCardStatement := sec7ZCard_of_inputs h51 aEx
  have hZV : Sec7ZVStatement := sec7ZV_of_parts zt centre h310chi
  have hSch : Sec7SchurStatement := sec7Schur_of_parts h34 h310chi centre hZV zcard
  have hK : Sec7CRWStatement := sec7CRW_of_inputs h34 h310chi h51 h52a aEx hSch
  have nOrder : Sec7NOrderStatement := sec7NOrder_of h34 h51 aEx hpts
  have h711S : Stroth711StrongStatement :=
    stroth711Strong_holds h34 h310root h52a nOrder aEx
  have hCommN : Sec7CommNStatement := sec7CommN_of_34 h34 h310 h311a
  have h78 : Stroth78Statement := stroth78Statement_holds
  have h79 : Stroth79Statement := stroth79Statement_holds
  have zn717 : Sec717ZNStatement :=
    sec717ZN_of_parts h51 aEx hpts h78 zcard hCommN h711S irrQ4NoPairing_holds
  have hHard : Step713O2HardStatement :=
    step713O2Hard_of_steps
      (step713XActs_of h52a h52b (stroth_5_2c_of_chi h310chi) aEx hpts h310chi zt zcard
          (sec7WVSecOrder_of_points hpts) h78
          (step713XActsPlus6_of h34 aEx hpts h52a h52b h310chi zt zcard))
      (step713Coprime_of h34 h311a h51 aEx hpts zt zcard h310chi h52a hK)
      (step713CentralN_of h79 zn717 h711S hSch h34 h51 h52a aEx zcard)
      (step713CentreFix_of centre hZV)
  have h712 : Stroth712Statement := stroth712Statement_holds
  exact stroth713_of_steps h712 (step713O2_of_hard h34 h51 aEx zt zcard hHard)

theorem tim81StrothUnRootStatement_holds_of_tim79a
    (h79 : Tim79aStatementWCQ) :
    Tim81StrothUnRootStatement :=
  tim81StrothUnRootStatement_holds_of_inputs
    (CFSG.RankThree.GF2n.Tim81.theorem1Statement_of_inputs h79)
    stroth712Statement_holds stroth713Statement_unconditional sec7CentreStatement_holds
    stroth34Statement_unconditional stroth311aStatement_unconditional
    sec7ZtStatement_holds
    (sec7ZCard_of_inputs stroth51Statement_unconditional sec7AExistsStatement_unconditional)

end Certs

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.RankThree.GF2n.Stroth80

section CertsTwo

theorem gf2nType_of_remaining_two
    (h79 : Tim79aStatementWCQ) (h98 : Stroth98Statement)
    (h108 : Stroth108Statement) (h1111 : Stroth1111Statement)
    (hCor2 : Tim77Cor2Statement) (hTim : Tim81StrothUnRootStatement) :
    GF2nTypeStatement :=
  gf2nType_of_remaining_thm1 h79 (stroth716TypeStatement_of_two hCor2 hTim)
    (stroth717Statement_of_two hCor2 hTim) h98 h108 h1111

theorem gf2nType_of_remaining_unRoot
    (h79 : Tim79aStatementWCQ) (h98 : Stroth98Statement)
    (h108 : Stroth108Statement) (h1111 : Stroth1111Statement)
    (hTim : Tim81StrothUnRootStatement) : GF2nTypeStatement :=
  gf2nType_of_remaining_two h79 h98 h108 h1111 tim77Cor2_holds hTim

theorem gf2nType_of_remaining_all
    (h79 : Tim79aStatementWCQ) (h98 : Stroth98Statement)
    (h108 : Stroth108Statement) (h1111 : Stroth1111Statement) : GF2nTypeStatement :=
  gf2nType_of_remaining_unRoot h79 h98 h108 h1111
    (tim81StrothUnRootStatement_holds_of_tim79a h79)

theorem gf2nType_of_remaining_three
    (h79 : Tim79aStatementWCQ) (h98 : Stroth98Statement)
    (h1111 : Stroth1111Statement) : GF2nTypeStatement :=
  gf2nType_of_remaining_all h79 h98 (stroth108Statement_of_h1111 h1111) h1111

end CertsTwo

end CFSG.RankThree.GF2n.Tim81
