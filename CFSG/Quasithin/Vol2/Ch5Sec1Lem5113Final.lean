module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113D4Lie
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Emb
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110Read
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Main
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113NA5F
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BlockD
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FFJM
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113ModOrth
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Hat7
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourZL
public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.H13.VolII16
public import CFSG.Quasithin.Vol2.Ch1EightTwoHubs
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113F5113

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt5_1_13_of_inputs
    (h312 : Vol2Native.A312ForSQTKCat) (hF : A314Facts) (hM23 : FactM23L34)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h331 : Stmt3_3_1) (hE22 : E2.E22StatementC)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hD42 : Stmt5_1_13_lie_D42C) (hC2 : FactC2Hall) (hTc : FactType513Aut) (hTe : FactType513Three)
    (hTp : FactType513Prime) (h325 : Stmt3_2_5) (h329 : Stmt3_2_9C) (hgen : FactA7Gen)
    (h5171 : A5.Stmt5_1_7_one) (h512 : Stmt5_1_2) (h5172 : Stmt5_1_7_two) (h51 : AsB51)
    (h511 : Stmt5_1_1) (hC126 : TheoremC126) (hbc : Stmt5_1_13_four_block_bc) (h513 : Stmt5_1_3)
    (h432 : Stmt4_3_2) : Stmt5_1_13C :=
  have hF513 : FactF5113 := F5113.factF5113_holds
  have h510 := stmt5_1_10_of_inputs h331 hE22 hGA
  have h37 := Vol2Native.a37ForSQTKCat_proved
  have h38 := Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact
    Vol2Native.a134SQTKFactCat Vol2Native.a36CoreForSQTKCat_proved h37
  have h5112 := stmt5_1_12_of_inputs h312 hF hM23 hP
    (Ch1Two.lemma128TwoAS_of_inputs (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
      (a312ForSQTK_of_cat h312) NQCat.lemma128One_holds)
  have hlie := stmt5_1_13_lieC_of_inputs hF513 hD42
  have hc2 := stmt5_1_13_c2_of h37 h38 NQCat.lemma128One_holds h510 hC2
  have hF318 : A318Facts := a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds
  have hhat := stmt5_1_13_type_hat7_of h37 h38 h510 hTe
  have hnq := stmt5_1_13_type_nq_of h37 h38 Vol2Native.a36ForSQTKCat_proved h510 hTc
  have hj1 := stmt5_1_13_type_j1_of h37 h38 Vol2Native.a36ForSQTKCat_proved h510 hlie
    factMathieuOrders_holds hM23 (a312ForSQTK_of_cat h312) hTc hTp
    (stmt5_1_13_type_j1_seven_of (a312ForSQTK_of_cat h312) h37 h38
      Vol2Native.a39ForSQTKCat_proved h325 (stmt3_2_8_of asB42_holds VolI.asI16Cover328_holds)
      h329 (stmt5_1_13_type_j1_ZK_of h37 h38 h510 h513 h432))
  have htype := stmt5_1_13_type_of h37 h38 VolI.a36ForSQTK_holds (a38ForSQTK_of_cat h38) hF318
    h510 hlie factMathieuOrders_holds hM23 (a312ForSQTK_of_cat h312) hnq hj1 hhat hTc hTe
  have hbe := stmt5_1_13_four_be_of h432 (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) hgen
    (stmt5_1_13_four_A7_of h5171 (factFFJ2M23_of h51))
    (stmt5_1_13_four_nat_of VolI.a36ForSQTK_holds (a37ForSQTK_of_cat h37)
      (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) h512 h5172
      (stmt5_1_13_four_ZK_of h5171 (factA7FF_of h51)) (stmt5_1_13_four_nA5_of h5171 h51
        (stmt5_1_13_four_nA5_four_of h5171 h51 h510))
      (stmt5_1_13_four_CZ_of h5171 h51 (stmt5_1_13_four_m4_of h5171 h51 h510)
        stmt5_1_13_four_ZL_of))
    (stmt5_1_13_four_block_of h511 h432 hC126 theoremC118 (stmt5_1_13_four_block_bcd_of hbc))
  have hfour := stmt5_1_13_four_of h37 h510 h5112 hlie htype (stmt5_1_13_four_star_of hbe)
  stmt5_1_13C_of h38 h510 h5112 hlie
    (stmt5_1_13_main_of h37 Vol2Native.a39ForSQTKCat_proved (a312ForSQTK_of_cat h312) h510 h5112
      hlie hc2 htype hfour (stmt5_1_13_mod_of_inputs h513 h432))

end CFSG.Quasithin.H13
