module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314NF
public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace Frontier331

theorem stmt3_3_13LTOn_of_frontier {P : NFSite}
    (h311 : Theorem311Stmt) (hNF : Obl3_3_13D12NFOn P) (hOut : Obl3_3_13D12NF_outer) :
    Stmt3_3_13LTOn P :=
  stmt3_3_13LTOn_of Vol2Native.a37ForSQTKCat_proved a38Cat (stmt3_3_10_of_frontier h311)
    prop134E9He_holds Vol2.Ch10.SecB.factL33M11 Vol2.Ch10.SecB.factL4L5 factAutL45Sylow_holds
    KGHe.factAutHeSylow_holds (Lem3313B.step3_3_13Bender_of Vol2Native.a37ForSQTKCat_proved a38Cat)
    (Lem3313Q.obl3_3_13LTOn_of_D12On Vol2Native.a37ForSQTKCat_proved a38Cat
      (Lem3313F.obl3_3_13D12On_of_nfOn hNF hOut))

theorem stmt3_3_14_of_frontier_on
    (h311 : Theorem311Stmt) (hN314 : Obl3_3_13D12NF_314) (hOut : Obl3_3_13D12NF_outer)
    (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B) : Stmt3_3_14 :=
  stmt3_3_14_of_b_on a38Cat Vol2Native.a39ForSQTKCat_proved (stmt3_3_10_of_frontier h311)
    (stmt3_3_13LTOn_of_frontier h311 hN314 hOut) h8one hI14

theorem step3_3_12R_of_frontier_on
    (h14 : Stmt3_3_14) (hList : Vol2Native.A312ListFactsCat) : Step3_3_12R :=
  step3_3_12R_of_inputs h14
    (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved) (a38ForSQTK_of_cat a38Cat)
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) (a312 hList)
    Vol2Native.a36ForSQTKCat_proved NQCat.lemma128One_holds

theorem step3_3_12RB_of_frontier_on
    (h14 : Stmt3_3_14) (hList : Vol2Native.A312ListFactsCat) : Step3_3_12RB :=
  step3_3_12RB_of_inputs h14
    (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved) (a38ForSQTK_of_cat a38Cat)
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) (a312 hList)
    Vol2Native.a36ForSQTKCat_proved NQCat.lemma128One_holds

theorem step3_3_15R_of_frontier_on
    (h14 : Stmt3_3_14) (hList : Vol2Native.A312ListFactsCat) : Step3_3_15R :=
  step3_3_15R_of stmt3_3_6_of_frontier h14 (step3_3_12R_of_frontier_on h14 hList)

theorem stmt3_3_16_of_frontier_on
    (h311 : Theorem311Stmt) (h14 : Stmt3_3_14) (hList : Vol2Native.A312ListFactsCat)
    (hC32 : ASInputs.AS_C_1_32) : Stmt3_3_16 :=
  L3316.stmt3_3_16_of_inputs stmt3_3_6_of_frontier h14 hC32 a38Cat
    Vol2Native.a39ForSQTKCat_proved B5.asB51_holds (stmt3_3_10_of_frontier h311)
    (step3_3_12RB_of_frontier_on h14 hList)
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

theorem stmt3_3_17_of_frontier_on
    (h311 : Theorem311Stmt) (h14 : Stmt3_3_14) (h8one : Stmt3_3_8One)
    (hList : Vol2Native.A312ListFactsCat) : Stmt3_3_17 :=
  stmt3_3_17_of stmt3_3_6_of_frontier (stmt3_3_8_of_frontier h8one)
    (stmt3_3_10_of_frontier h311) (step3_3_12R_of_frontier_on h14 hList) h14

theorem stmt3_3_22_of_frontier_on
    (h311 : Theorem311Stmt) (h14 : Stmt3_3_14) (h8one : Stmt3_3_8One)
    (hList : Vol2Native.A312ListFactsCat)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) :
    Stmt3_3_22 :=
  stmt3_3_22_of (stmt3_3_5_of a38Cat Vol2Native.a39ForSQTKCat_proved)
    (stmt3_3_7_of a38Cat Vol2Native.a39ForSQTKCat_proved) (stmt3_3_8_of_frontier h8one)
    (stmt3_3_10_of_frontier h311) h14 (stmt3_3_17_of_frontier_on h311 h14 h8one hList) a38Cat
    Vol2Native.a39ForSQTKCat_proved (a38ForSQTK_of_cat a38Cat)
    (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) hC27

end Frontier331

end CFSG.Quasithin.H13
