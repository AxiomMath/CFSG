module

public import CFSG.RankThree.GF2n.Stroth80.Sec85Sylow
public import CFSG.RankThree.GF2n.Stroth80.Sec86NormH
public import CFSG.RankThree.GF2n.Stroth80.Sec84StrongClosure
public import CFSG.RankThree.GF2n.Stroth80.Sec86MinOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec84CaseOne
public import CFSG.RankThree.GF2n.Stroth80.Sec8V1InterDim
public import CFSG.RankThree.GF2n.Stroth80.Sec84Leaves
public import CFSG.RankThree.GF2n.Stroth80.Sec51Of34
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsAssembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

structure Sec84LeavesE : Prop where
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
  lemmaH : Sec8LemmaHStatement
  caseU : Sec84CommUpperStatement
  caseNA : Sec84NAbelianStatement
  firstV : Step85FirstVStatement
  comm : Step85CommStatement
  tim81 : Tim81StrothSpStatement
  hypSub : Step86HypSubStatement
  notUnitary : Step86NotUnitaryStatement

theorem sec84Leaves_of_E (L : Sec84LeavesE) : Sec84Leaves := by
  have hPts : Sec5NatPointsSpStatement := sec5NatPointsSp_of_34 L.h34
  have hDim : Sec8V1InterDimStatement :=
    sec8V1InterDim_of L.h51 L.aExists L.zt L.h310chi L.h53.1
  have hStrong : Sec8StrongClosureStatement :=
    sec8StrongClosure_of L.h51 L.aExists L.zt L.h310chi L.h53 stroth56Sp_holds hDim L.lemmaH
  have hTI : Sec8TIStatement := sec8TI_of_inputs L.h51 L.aExists L.zt L.h310chi
  have hMin : Sec86MinOrderStatement := sec86MinOrder_of L.h51 L.aExists hPts
  have hirr : Sec86IrredStatement := sec86Irred_of_inputs L.h83 L.h51 L.aExists hMin
  have hFirst : Step85FirstStatement :=
    step85First_of_parts L.zt L.h51 L.aExists L.hNt L.firstV
  exact
    { h51 := L.h51
      h82 := L.h82
      h83 := L.h83
      hNt := L.hNt
      aExists := L.aExists
      ti := hTI
      zt := L.zt
      h56 := stroth56Sp_holds
      minOrder := hMin
      normH := sec86NormH_of L.h34 L.h51 L.aExists L.h54 L.hge hTI hStrong
      case1 := step84CaseOne_of_leaves L.h51 L.aExists hPts hirr hTI L.caseU L.caseNA
      case2 := step84CaseTwo_of_strong hStrong
      f2 := step85F2_holds L.h34 L.h51 L.aExists L.zt L.h54 L.hge
      firstV := L.firstV
      comm := L.comm
      sylow := step85Sylow_of_first L.h51 L.aExists L.zt L.h310chi hFirst
      tim81 := L.tim81
      hypSub := L.hypSub
      notUnitary := L.notUnitary }

end CFSG.RankThree.GF2n.Stroth80
