module

public import CFSG.Quasithin.Vol2.Ch7Sp4PairA6
public import CFSG.Quasithin.Vol2.Ch7SL3Pair
public import CFSG.Quasithin.Vol2.Ch7Lem755
public import Certificates.Certificate113
public import Certificates.Certificate7022
public import Certificates.Certificate7024
public import Certificates.Certificate7026
public import Certificates.Certificate7067
public import CFSG.Quasithin.Vol2.Ch7Lem761End
public import CFSG.Quasithin.Vol2.Ch7Lem771
public import CFSG.Quasithin.Vol2.Ch7Lem735
public import CFSG.Quasithin.Vol2.Ch7Lem741
public import CFSG.Quasithin.Vol2.Ch7Lem754
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch7NotFFS7

public section

namespace CFSG.Quasithin.H13

theorem stmt7_0_1_of_inputs_771
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hshape : Stmt7_0_1_shapeC)
    (h711 : Stmt7_1_1) (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5)
    (h3228 : Stmt3_2_2_eight) (h734 : Stmt7_3_4)
    (hM22 : Stmt7_2_1_M22Hat) (hM12 : Stmt7_2_1_M12) (hM23 : Stmt7_2_1_M23Code)
    (hin : Input8_1_2) (h755 : Input7_5_5)
    (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12) (h773 : Stmt7_7_3) (h772 : Stmt7_7_2)
    (h3104 : Stmt3_2_10_four) (h3106 : Stmt3_2_10_six) (h813 : Stmt8_1_3_M24)
    (h8213 : Stmt8_2_13_cocode) (h8214 : Stmt8_2_14) (h831 : Stmt8_3_1) (h9 : Stmt9_omegaPlus) :
    Stmt7_0_1 :=
  have hmod : StmtFSUModule := stmtFSUModule_of_eight h3228
  stmt7_0_1_of_chain hmod hshape h711
    (stmt7_3_5_of_E63 h37 h38 h39 hmod h711n h325 h3228 h63 h734)
    (stmt7_5_2_of_input812 h37 h38 h39 hmod h711n h325 h734 hin hM22)
    (stmt7_5_4_of h37 h38 h39 hmod h711n h325 h734 hin hM12 hM23)
    (stmt7_5_5_of h37 h38 h39 hmod h711n h325 h734 hin h755)
    (stmt7_6_1_of h37 h38 h39 hmod h711n h325 h734
      (stmt7_7_1_of h37 h38 h39 hmod h711n h325 h3228 h612 h773) h772 h3104 h3106)
    h813 h8213 h8214 h831 h9

end CFSG.Quasithin.H13
