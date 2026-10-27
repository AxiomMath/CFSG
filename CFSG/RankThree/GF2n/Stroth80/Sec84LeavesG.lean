module

public import CFSG.RankThree.GF2n.Stroth80.Sec86HypSub
public import CFSG.RankThree.GF2n.Stroth80.Sec84CommUpper
public import CFSG.RankThree.GF2n.Stroth80.Sec86NotUnitary
public import CFSG.RankThree.GF2n.Stroth80.Sec86PSU6TwoPart
public import CFSG.RankThree.GF2n.Stroth80.Sec84LeavesE
public import CFSG.RankThree.GF2n.Stroth80.Sec8HMain

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

structure Sec84LeavesE' : Prop where
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
  caseNA : Sec84NAbelianStatement
  firstV : Step85FirstVStatement
  comm : Step85CommStatement
  tim81 : Tim81StrothSpStatement
  psu6Out : PSU6OutSolvableStatement

theorem sec84LeavesE_of_E' (L : Sec84LeavesE') : Sec84LeavesE := by
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
      lemmaH := sec8LemmaH_of L.h34 (stroth310Root_of_34 L.h34) L.h51 L.h53 L.h310chi
      caseU := sec84CommUpper_of L.h34 L.h51 L.h53 hPts L.aExists
      caseNA := L.caseNA
      firstV := L.firstV
      comm := L.comm
      tim81 := L.tim81
      hypSub := step86HypSub_of L.h34 L.h51 L.aExists L.zt hirr
      notUnitary := step86NotUnitary_of L.h34 L.h51 L.aExists L.h83 hirr L.psu6Out
          psu6TwoPart_holds }

theorem sec84Leaves_of_E' (L : Sec84LeavesE') : Sec84Leaves :=
  sec84Leaves_of_E (sec84LeavesE_of_E' L)

end CFSG.RankThree.GF2n.Stroth80
