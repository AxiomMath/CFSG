module

public import CFSG.RankThree.GF2n.Stroth80.Sec84LeavesG
public import CFSG.RankThree.GF2n.Stroth80.Sec85FirstV
public import CFSG.RankThree.GF2n.Stroth80.Sec85Comm
public import CFSG.RankThree.GF2n.Stroth80.Sec84NA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


structure Sec84LeavesF : Prop where
  h34 : Stroth34Statement
  h51 : Stroth51Statement
  h53 : Stroth53Statement
  h54 : Stroth54Statement
  h82 : Stroth82Statement
  h83 : Stroth83Statement
  hNt : StrothNtStatement
  hge : Stroth6NbarGeStatement
  h310chi : Stroth310ChiStatement
  aExists : Sec8AExistsStatement
  zt : Sec8ZtStatement
  sp6 : Sp6NoEmbeddingStatement
  cw1 : Sec53CentralizerW1Statement
  tim81 : Tim81StrothSpStatement
  psu6Out : PSU6OutSolvableStatement

theorem sec84NAbelian_of_leavesF (L : Sec84LeavesF) : Sec84NAbelianStatement :=
  sec84NAbelian_of_inputs L.h34 L.h51 L.h53 L.h310chi L.zt L.aExists L.h83 L.cw1 L.sp6

theorem stroth84_of_leavesF (L : Sec84LeavesF) : Stroth84Statement := by
  have hPts : Sec5NatPointsSpStatement := sec5NatPointsSp_of_34 L.h34
  have hDim : Sec8V1InterDimStatement :=
    sec8V1InterDim_of L.h51 L.aExists L.zt L.h310chi L.h53.1
  have hLemmaH : Sec8LemmaHStatement :=
    sec8LemmaH_of L.h34 (stroth310Root_of_34 L.h34) L.h51 L.h53 L.h310chi
  have hStrong : Sec8StrongClosureStatement :=
    sec8StrongClosure_of L.h51 L.aExists L.zt L.h310chi L.h53 stroth56Sp_holds hDim hLemmaH
  have hTI : Sec8TIStatement := sec8TI_of_inputs L.h51 L.aExists L.zt L.h310chi
  have hMin : Sec86MinOrderStatement := sec86MinOrder_of L.h51 L.aExists hPts
  have hirr : Sec86IrredStatement := sec86Irred_of_inputs L.h83 L.h51 L.aExists hMin
  have hConj : Sec86ConjStatement := sec86Conj_of_parts stroth56Sp_holds L.zt L.h51 L.aExists
  exact stroth84_of_cases L.h82 L.h83 hConj
    (step84CaseOne_of_leaves L.h51 L.aExists hPts hirr hTI
      (sec84CommUpper_of L.h34 L.h51 L.h53 hPts L.aExists) (sec84NAbelian_of_leavesF L))
    (step84CaseTwo_of_strong hStrong)

theorem sec84LeavesE'_of_F (L : Sec84LeavesF) : Sec84LeavesE' :=
  { h34 := L.h34
    h51 := L.h51
    h53 := L.h53
    h54 := L.h54
    h82 := L.h82
    h83 := L.h83
    hNt := L.hNt
    hge := L.hge
    h310chi := L.h310chi
    aExists := L.aExists
    zt := L.zt
    caseNA := sec84NAbelian_of_leavesF L
    firstV := step85FirstV_of_83 L.h34 L.h51 L.h53 L.h310chi L.zt L.aExists L.h83
    comm := step85Comm_of L.h34 L.h51 L.h53 L.h310chi L.zt L.aExists L.h83
      (stroth84_of_leavesF L)
    tim81 := L.tim81
    psu6Out := L.psu6Out }

theorem sec84Leaves_of_F (L : Sec84LeavesF) : Sec84Leaves :=
  sec84Leaves_of_E' (sec84LeavesE'_of_F L)

theorem sec84_of_leavesF (L : Sec84LeavesF) :
    Stroth84Statement ∧ Stroth85Statement ∧ Stroth86Statement :=
  sec84_of_leaves (sec84Leaves_of_F L)

end CFSG.RankThree.GF2n.Stroth80
