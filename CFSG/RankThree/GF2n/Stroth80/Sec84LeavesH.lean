module

public import CFSG.RankThree.GF2n.Stroth80.Sec84LeavesF
public import CFSG.RankThree.GF2n.Stroth80.Sec716NoLargeUnitary
public import CFSG.RankThree.GF2n.Stroth80.Sec53CwFromFix
public import CFSG.RankThree.GF2n.Stroth80.Sec53cFixPair
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Final

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank


structure Sec84LeavesH : Prop where
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
  tim81SpRoot : Tim81StrothSpUnRootStatement
  psu6Out : PSU6OutSolvableStatement

theorem sec84LeavesF_of_H (L : Sec84LeavesH) : Sec84LeavesF := by
  have hPts : Sec5NatPointsSpStatement := sec5NatPointsSp_of_34 L.h34
  have hMin : Sec86MinOrderStatement := sec86MinOrder_of L.h51 L.aExists hPts
  have hirr : Sec86IrredStatement := sec86Irred_of_inputs L.h83 L.h51 L.aExists hMin
  exact
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
      sp6 := Sp6NoEmb.sp6NoEmbedding_holds
      cw1 := sec53CentralizerW1_of_fix L.h34 (stroth310Root_of_34 L.h34) L.h51
        (stroth53FixB_holds L.h34 (stroth310Root_of_34 L.h34) L.h51)
        (stroth53FixC_holds L.h34 (stroth310Root_of_34 L.h34) L.h51)
      tim81 := tim81StrothSp_of_root L.tim81SpRoot
        (sec86NoLargeUnitaryRoot_of L.h83 L.zt (sec86ZCard_of_51 L.h51 L.aExists)) L.h83 hirr
      psu6Out := L.psu6Out }

theorem sec84_of_leavesH (L : Sec84LeavesH) :
    Stroth84Statement ∧ Stroth85Statement ∧ Stroth86Statement :=
  sec84_of_leavesF (sec84LeavesF_of_H L)

end CFSG.RankThree.GF2n.Stroth80
