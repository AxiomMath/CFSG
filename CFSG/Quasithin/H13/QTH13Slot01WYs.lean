module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptMain
public import CFSG.Quasithin.MS93.C134L32CorrMHolds
public import CFSG.Quasithin.H13.QTH13Slot11C132
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LHolds
public import CFSG.Quasithin.Background.SmithC27Holds
public import CFSG.Quasithin.Background.F618Holds
public import CFSG.Quasithin.Vol2.Ch10Reselect.ReselectHolds
public import CFSG.Yardstones.M64f425cd8476.Definitions
public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierNF
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3319G
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3321NF
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3324B
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa1

public section

namespace CFSG.Quasithin.H13

namespace Frontier331

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)

theorem stmt3_3_1_holds

    : Stmt3_3_1 := by
  have h38 : A38ForSQTKCat := a38Cat
  have h39 : A39ForSQTKCat := Vol2Native.a39ForSQTKCat_proved
  have h5 := stmt3_3_5_of a38Cat Vol2Native.a39ForSQTKCat_proved
  have h7 := stmt3_3_7_of a38Cat Vol2Native.a39ForSQTKCat_proved
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hNa2 : Obl3_3_13D12NF_a2 := NFa2.obl3_3_13D12NF_a2_holds VolI.a36ForSQTK_holds h5 h7
    stmt3_3_9_of hGA lemma128Two_proved Vol2Native.a37ForSQTKCat_proved a38Cat
    Vol2Native.a39ForSQTKCat_proved
  have hNa2n : Obl3_3_13D12NF_a2_nine := NFa2.obl3_3_13D12NF_a2_nine_holds VolI.a36ForSQTK_holds
    h5 h7 stmt3_3_9_of hGA lemma128Two_proved Vol2Native.a37ForSQTKCat_proved a38Cat
    Vol2Native.a39ForSQTKCat_proved
  have hC32 : ASInputs.AS_C_1_32 := asC132_holds
  have hC34 : C134L32CorrM := MS93.c134L32CorrM_holds
  have hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G :=
    asc27Statement_of_c132 asC132_holds
  have hF : F6.TheoremF618Cat := F6.theoremF618Cat_holds
  have hI14 : Insp3_3_14B := Ins314.insp3_3_14B_of Vol2Native.a37ForSQTKCat_proved a38Cat
  have h8one : Stmt3_3_8One := stmt3_3_8One_of_b56 a38Cat Vol2Native.a39ForSQTKCat_proved
    asB56_holds VolI.a38TypesSLThree_holds
  have hOut : Obl3_3_13D12NF_outer :=
    Lem3313Q.obl3_3_13D12NF_outer_of Vol2Native.a37ForSQTKCat_proved a38Cat
      KGAutSyl.factAutL2pOuter_holds
  have hN314 : Obl3_3_13D12NF_314 := L3314.obl3_3_13D12NF_314_of VolI.a36ForSQTK_holds h5 h7
    lemma128Two_proved Vol2Native.a37ForSQTKCat_proved a38Cat Vol2Native.a39ForSQTKCat_proved
    NF314pt.obl3_3_13D12NF_314pt_holds
  have h14 := stmt3_3_14_of_frontier_on theorem311 hN314 hOut h8one hI14
  have he : Step3_3_21e :=
    L3321.step3_3_21e_of h5 h14 hGA (L3321.step3_3_21d_of h5 h7 stmt3_3_9_of h14)
  have hNa1 : Obl3_3_13D12NF_a1 := L3321.obl3_3_13D12NF_a1_of VolI.a36ForSQTK_holds h7 h14 he
  have h13a : Stmt3_3_13LTOn Site3321a1 := stmt3_3_13LTOn_of_frontier theorem311 hNa1 hOut
  have h13b : Stmt3_3_13LTOn Site3321a2 :=
    stmt3_3_13LTOn_of_frontier theorem311 (obl3_3_13D12NFOn_a2_of hNa2 hNa2n) hOut
  have h20 := stmt3_3_20_of_frontier theorem311 hF a312List
  have h12R := step3_3_12R_of_frontier_on h14 a312List
  have h15R := step3_3_15R_of_frontier_on h14 a312List
  have h18 : Stmt3_3_18 :=
    L3318.stmt3_3_18_ofW h14 hGA a38Cat Vol2Native.a39ForSQTKCat_proved h12R h15R hC34 h20
  have h19 : Stmt3_3_19 :=
    L3319.stmt3_3_19_ofW h14 hGA a38Cat Vol2Native.a39ForSQTKCat_proved h12R h15R hC34 h20
      B5.asB51_holds VolI.asI16Cover_holds
  have h21 : Stmt3_3_21 := stmt3_3_21_of_onW h5 h7 stmt3_3_9_of h13a h13b h14 h18 h20
    B5.asB51_holds VolI.asI16Cover_holds a38Cat Vol2Native.a39ForSQTKCat_proved hGA h15R hC34 h12R
    (L3321.step3_3_21fQ_of h7 h14 hGA he)
  have hO24 : Obs3_3_24 := obs3_3_24_of a38Cat Vol2Native.a39ForSQTKCat_proved B5.asB51_holds
    (stmt3_3_10_of_frontier theorem311) h14 (stmt3_3_16_of_frontier_on theorem311 h14 a312List hC32)
    h19 h21 (stmt3_3_22_of_frontier_on theorem311 h14 h8one a312List hC27) hC32
  have hE := HatE.hatA6Embed_holds
  have hN := HatN.hatA6Normalizer_holds
  have hXS3 := HatX.fact3_3_25XS3Hat_of h38 h39 hE hN
  have hHat := HatB.insp3_3_25Hat_of h38 h39 (HatQ.insp3_3_25HatRest_of h38 h39 hE hN)
  have hS23 := step3_3_23_ofW h38 h39 h14 hC34
    (C4Fix3323.notCase4Corr3323_holdsW h38 h39 h14 h20 hC34)
  have hS24 := step3_3_24_ofW h38 h39 h14 hC34 h20
  have h23 := stmt3_3_23_of h38 h39 h20 hS23
  have h24 := stmt3_3_24_of h23 hO24 hS24
  have hF318 : A318Facts := a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds
  have hθ := fact3_3_25Theta_of hF318 VolI.a36ForSQTK_holds (a38ForSQTK_of_cat h38)
  have hX := CZA6.fact3_3_25XS3_of h38 h39 (CZA6.fact3_3_25XS3Rest_of h38 h39 B5.asB51_holds hXS3)
  have hT := ThreeL32.insp3_3_25Three_of h38 h39
    (ThreeL32.insp3_3_25ThreeRest_holds h38 h39 B5.asB51_holds)
  have hI := CZA6.insp3_3_27_of h38 h39 (CZA6.insp3_3_27Rest_holds h38 h39 B5.asB51_holds)
  have h25 := stmt3_3_25_of h38 h39 h14 h24 hθ hX hHat hT
  have h27 := stmt3_3_27_of h38 h39 h14 h25 factL32CentralInv_holds hI
  have hS28 := G2Step28.step3_3_28G2_of h38 h39 B5.asB51_holds h25 h27
  have h26 := stmt3_3_26_of h38 h39 h14 h25
  have h28L := stmt3_3_28L32_of h38 h39 h14 h23 h25 h26 h27
  have h29 := stmt3_3_29_of h38 h39 h14 h23 h25 h28L
  have h28TC := stmt3_3_28G2TC_of h38 h39 h14 h25 h26 h29 hS28
  have h28G := stmt3_3_28G2_of h25 h28TC
  have h30 := stmt3_3_30_of_h h38 h39 h14 h25 h28G h29
    (Lem3330H.insp3_3_30H_of h38 h39 B5.asB51_holds)
  have h31 := stmt3_3_31_of h38 h39 h14 h26 h27 h30 (Lem3331S.step3_3_31S_of h38 h39 h25 h27)
    (Lem3331E4.step3_3_31E4_of h38 h39 h25 h27)
  have h32 := stmt3_3_32_of h38 h39 h14 h20 h30 h31 (insp3_3_32Mod_holds h38 h39)
    (insp3_3_32Par_holds h38 h39)
  exact stmt3_3_1_of Vol2Native.a37ForSQTKCat_proved a38Cat Vol2Native.a39ForSQTKCat_proved
    (stmt3_3_1A_of_inputs h38 h39 h14 h30 h31 h32 (inspClose_holds h38 h39))
    Cor332.stmt3_3_2MTwo_holds

end Frontier331

theorem ys01_of_holds
    : CFSG.Yardstones.M64f425cd8476.Chapter3Theorems :=
  ⟨Frontier331.stmt3_3_1_holds, CFSG.Quasithin.Vol2.Ch10Reselect.ch10Reselect_holds⟩

end CFSG.Quasithin.H13
