module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseA
import CFSG.RankThree.GF2n.Stroth80.Sec7Stroth78Holds
import CFSG.RankThree.GF2n.Stroth80.Sec7Unconditional
import CFSG.RankThree.GF2n.Stroth80.Sec717ZNProof
import CFSG.RankThree.GF2n.Stroth80.Sec715ZNModel
import CFSG.RankThree.GF2n.Stroth80.Sec715ZNComm
import CFSG.RankThree.GF2n.Stroth80.IrrQ4Holds
import CFSG.RankThree.GF2n.Stroth80.Sec714ModelN12
import CFSG.RankThree.GF2n.Stroth80.StatedOmegaPerfect
import CFSG.RankThree.GF2n.Stroth80.QuadraticPlusTypeDickson
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Binders

theorem sec79MinOrderStatement_holds : Sec79MinOrderStatement :=
  sec79MinOrder_of stroth51Statement_unconditional sec7AExistsStatement_unconditional
    (sec5NatPointsOmega_of stroth34Statement_unconditional
      (stroth310Root_of_34 stroth34Statement_unconditional))

end Binders

section Certs

theorem sec717ZNStatement_holds : Sec717ZNStatement :=
  sec717ZN_of_parts stroth51Statement_unconditional sec7AExistsStatement_unconditional
    (sec5NatPointsOmega_of stroth34Statement_unconditional
      (stroth310Root_of_34 stroth34Statement_unconditional))
    stroth78Statement_holds
    (sec7ZCard_of_inputs stroth51Statement_unconditional sec7AExistsStatement_unconditional)
    (sec7CommN_of_34 stroth34Statement_unconditional stroth310Statement_unconditional
      stroth311aStatement_unconditional)
    stroth711StrongStatement_holds irrQ4NoPairing_holds

theorem step715ZNStatement_holds : Step715ZNStatement := by
  have h34 : Stroth34Statement := stroth34Statement_unconditional
  have h310 : Stroth310Statement := stroth310Statement_unconditional
  have h311a : Stroth311aStatement := stroth311aStatement_unconditional
  have h51 : Stroth51Statement := stroth51Statement_unconditional
  have hA : Sec7AExistsStatement := sec7AExistsStatement_unconditional
  have hA8 : Sec8AExistsStatement := sec8AExistsStatement_unconditional
  have h52a : Stroth52aStatement := stroth52aStatement_holds
  have h52b : Stroth52bStatement := stroth52bStatement_holds
  have h310chi : Stroth310ChiStatement := stroth310Chi_of_34 h34
  have h310root : Stroth310RootStatement := stroth310Root_of_34 h34
  have h56 : Stroth56NatStatement := stroth56Nat_of_34 h34
  have hpts : Sec5NatPointsOmegaStatement := sec5NatPointsOmega_of h34 h310root
  have hptsSp : Sec5NatPointsSpStatement := sec5NatPointsSp_of_34 h34
  have centre : Sec7CentreMpStatement := sec7CentreMp_of_inputs h51 h52a hA
  have zt : Sec7ZtStatement :=
    sec7Zt_of_inputs h34 h310 h51 h52a hA hA8 h56 hpts hptsSp
  have zcard : Sec7ZCardStatement := sec7ZCard_of_inputs h51 hA
  have hZV : Sec7ZVStatement := sec7ZV_of_parts zt centre h310chi
  have hSch : Sec7SchurStatement := sec7Schur_of_parts h34 h310chi centre hZV zcard
  have hK : Sec7CRWStatement := sec7CRW_of_inputs h34 h310chi h51 h52a hA hSch
  have nOrder : Sec7NOrderStatement := sec7NOrder_of h34 h51 hA hpts
  have hCommN : Sec7CommNStatement := sec7CommN_of_34 h34 h310 h311a
  have h711S : Stroth711StrongStatement := stroth711StrongStatement_holds
  have h78 : Stroth78Statement := stroth78Statement_holds
  have h714 : Stroth714Statement :=
    stroth714_of_inputs h78
      (step714NotTwelve_of_model
        (S714.sec714Model_of
          ⟨h34, h310root, h310chi, h51, h52a, h52b, nOrder, zcard, hK, centre, hZV⟩
          h711S hA hpts)
        statedOmegaPlusFourPerfect_holds (quadraticPlusType_of_dickson dicksonOmegaPlusFour_holds))
  exact step715ZN_of_model
    (sec715ZNModel_of h34 h310root h310chi h51 h52a h52b nOrder zcard hK centre hCommN
      hA hpts h711S)
    (sec715Split_of_comm (sec715ZNComm_holds h51 hA hpts nOrder h711S) h51 hA hpts)
    h714 h711S statedOmegaPlusFourPerfect_holds
    (quadraticPlusType_of_dickson dicksonOmegaPlusFour_holds)

end Certs

end CFSG.RankThree.GF2n.Stroth80
