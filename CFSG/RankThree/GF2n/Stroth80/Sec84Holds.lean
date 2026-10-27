module

public import CFSG.RankThree.GF2n.Stroth80.Sec82Holds
public import CFSG.RankThree.GF2n.Stroth80.Sec53CwFromFix
public import CFSG.RankThree.GF2n.Stroth80.Sec86Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Final
public import CFSG.RankThree.GF2n.Stroth80.Sec84Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec84CaseOne
public import CFSG.RankThree.GF2n.Stroth80.Sec84CommUpper
public import CFSG.RankThree.GF2n.Stroth80.Sec84NA
public import CFSG.RankThree.GF2n.Stroth80.Sec86MinOrder

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs


theorem sec86IrredStatement_holds : Sec86IrredStatement :=
  sec86Irred_of_inputs stroth83Statement_holds stroth51Statement_unconditional
    sec8AExistsStatement_unconditional
    (sec86MinOrder_of stroth51Statement_unconditional sec8AExistsStatement_unconditional
      (sec5NatPointsSp_of_34 stroth34Statement_unconditional))

theorem stroth84Statement_holds : Stroth84Statement := by
  have hPts : Sec5NatPointsSpStatement := sec5NatPointsSp_of_34 stroth34Statement_unconditional
  have hDim : Sec8V1InterDimStatement :=
    sec8V1InterDim_of stroth51Statement_unconditional sec8AExistsStatement_unconditional
      sec8ZtStatement_holds (stroth310Chi_of_34 stroth34Statement_unconditional)
      stroth53Statement_unconditional.1
  have hLemmaH : Sec8LemmaHStatement :=
    sec8LemmaH_of stroth34Statement_unconditional
      (stroth310Root_of_34 stroth34Statement_unconditional) stroth51Statement_unconditional
      stroth53Statement_unconditional (stroth310Chi_of_34 stroth34Statement_unconditional)
  have hStrong : Sec8StrongClosureStatement :=
    sec8StrongClosure_of stroth51Statement_unconditional sec8AExistsStatement_unconditional
      sec8ZtStatement_holds (stroth310Chi_of_34 stroth34Statement_unconditional)
      stroth53Statement_unconditional stroth56Sp_holds hDim hLemmaH
  have hTI : Sec8TIStatement :=
    sec8TI_of_inputs stroth51Statement_unconditional sec8AExistsStatement_unconditional
      sec8ZtStatement_holds (stroth310Chi_of_34 stroth34Statement_unconditional)
  have hConj : Sec86ConjStatement :=
    sec86Conj_of_parts stroth56Sp_holds sec8ZtStatement_holds stroth51Statement_unconditional
      sec8AExistsStatement_unconditional
  have hCW : Sec53CentralizerW1Statement :=
    sec53CentralizerW1_of_fix stroth34Statement_unconditional
      (stroth310Root_of_34 stroth34Statement_unconditional) stroth51Statement_unconditional
      (stroth53FixB_holds stroth34Statement_unconditional
        (stroth310Root_of_34 stroth34Statement_unconditional) stroth51Statement_unconditional)
      (stroth53FixC_holds stroth34Statement_unconditional
        (stroth310Root_of_34 stroth34Statement_unconditional) stroth51Statement_unconditional)
  have hNA : Sec84NAbelianStatement :=
    sec84NAbelian_of_inputs stroth34Statement_unconditional stroth51Statement_unconditional
      stroth53Statement_unconditional (stroth310Chi_of_34 stroth34Statement_unconditional)
      sec8ZtStatement_holds sec8AExistsStatement_unconditional stroth83Statement_holds hCW
      Sp6NoEmb.sp6NoEmbedding_holds
  exact stroth84_of_cases stroth82Statement_holds stroth83Statement_holds hConj
    (step84CaseOne_of_leaves stroth51Statement_unconditional sec8AExistsStatement_unconditional
      hPts sec86IrredStatement_holds hTI
      (sec84CommUpper_of stroth34Statement_unconditional stroth51Statement_unconditional
        stroth53Statement_unconditional hPts sec8AExistsStatement_unconditional) hNA)
    (step84CaseTwo_of_strong hStrong)

end Certs

end CFSG.RankThree.GF2n.Stroth80
