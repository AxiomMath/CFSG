module

public import CFSG.Quasithin.H13.A6S13827Gm
public import CFSG.Quasithin.H13.A6S13827hWA5

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

theorem lem13827G2_of_root5W_A5
    (h331 : CFSG.Quasithin.H13.Stmt3_3_1) (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2)
    (h12213 : CFSG.Quasithin.H13.Stmt12_2_13) (h13315 : Stmt13_3_15)
    (h523 : CFSG.Quasithin.H13.Stmt5_2_3) (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    (hcorr : CFSG.Quasithin.MS93.C134Weak)
    (hC137 : CFSG.Quasithin.H13.U3.GC137.C137StatementFiveSQTK)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5)
    (h48 : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC48Statement G)
    (hZ437 : CFSG.Quasithin.H13.Ch4.Gap437Sp4Z) (hAut : Fact13820Aut)
    (hHat6 : Case13821Hat6) (hHatM22 : Case13821HatM22) (hL32Hat : Case13821L32Hat) :
    Lem13827G2 := by
  have h13314 : Stmt13_3_14 :=
    stmt13_3_14_of_root5W_A5 h331 h1332 h1222 h12213 h523 hC132 hcorr hC137 hA5 h48 hZ437
  have ha : Case13820a := case13820a_holds h1332 h1222 h13314 h13315
  have hb : Case13820bSL34U38 := case13820bSL34U38_holds h1332 h1222 h13314 h13315
  have hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G) :=
    C124.c124StatementSQTK_of_e22 e22StatementNoN_proved
  have h1356two : Input1356Two :=
    input1356Two_of h1222 (input1356TwoS6_of_sqtk hC124 h1222 (input1356TwoS6Block_of h13315))
  have h36c := Vol2Native.a36CoreForSQTKCat_proved
  have h37c := Vol2Native.a37ForSQTKCat_proved
  have h39c := Vol2Native.a39ForSQTKCat_proved
  have h38c := Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat h36c h37c
  have h37 : A37ForSQTK := a37ForSQTK_of_cat h37c
  have h38 : A38ForSQTK := a38ForSQTK_of_cat h38c
  have h36 : A36ForSQTK := VolI.a36ForSQTK_holds
  have hA21 : AsA21SQTKSection := asA21SQTKSection
  have hF318 : A318Facts := a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds
  have hB42 := CFSG.Quasithin.asB42_holds
  have hB45 := CFSG.Quasithin.asB45_holds
  have h56 : AsB56 := CFSG.Quasithin.asB56_holds
  have hD310 : D310 := CFSG.Quasithin.H13.d310_holds
  have hD391D := d391Deep_of_inputs
      (d35_of_inputs asB42_holds B5.asB51_holds asB56_holds asA21SQTKSection asA36NoOddCover_holds
          (d35InspTwo_of_B51 B5.asB51_holds) d35InspSum_holds
          (d35InspUniq_of_chk (d35InspUniq8_of_chk d35ValChk_run) d35Chk_run)
          (d35InspB42_of_orbit asA21SQTKSection (F918X.d35InspOrbit_proved asA21SQTKSection)))
      B5.asB51_holds asA21SQTKSection
  have hD391 : D391 := CFSG.Quasithin.d391L_of_deep (hD := hD391D)
  have hI4 : Insp4 := CFSG.Quasithin.insp4_of_inputs (hA21 := hA21)
    (hG2 := CFSG.Quasithin.factG2Cayley_holds) (h42 := hB42) (h45 := hB45) (hD310 := hD310)
  have hD37 : D37 := CFSG.Quasithin.d37_holds
  have hF10 := CFSG.Quasithin.Vol2.Ch10.SecA.facts10_1_holds
  have hX5 := CFSG.Quasithin.insp5aNonShape_holds
  have hD321 : D321 := CFSG.Quasithin.d321_proved
    (CFSG.Quasithin.d3L38_of_a38 (h := CFSG.Quasithin.d3A38_holds)) h38c
    CFSG.Quasithin.SmithD39Two.d36c_holds
    (CFSG.Quasithin.d310Deep_of_unfaithfulD (h391 := hD391D)
      (hU := CFSG.Quasithin.d310Unfaith_holds))
    (CFSG.Quasithin.d392_of_suzuki (hS := CFSG.Quasithin.d392Suzuki_of_d38
      (h38 := CFSG.Quasithin.SmithD39Two.d38Top_holds)))
    hB42 hB45 h56 hA21 hF10 hX5
  have hI5 : Insp5a := CFSG.Quasithin.insp5a_of_inputs (hA21 := hA21) (h45 := hB45) (hF := hF10)
    (hX := hX5)
  have h323 : Stmt3_2_3 := stmt3_2_3_of h37c h38c h39c
  have h1226 : Stmt12_2_6 := stmt12_2_6_of h1222 h323
  have h1228 : Stmt12_2_8 := stmt12_2_8_of h1222 hF318 h38
  have h139 : Stmt13_3_9 :=
    U3.stmt13_3_9_of_1332 h1332 h1226 h1228 (U3.stmt13_2_2_9L1_holds h1332)
  have h1334 : Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have h1337 : Stmt13_3_7 := U3.stmt13_3_7_of h1332 h1228
  have h13 : Lem13813 := lem13813_holds h13314 h13315 h1356two h139
  have h16 : Lem13816 := lem13816_holds h36c h37 h38 lemma122A_holds h139 h1334 h1337 h13
    d36_holds hD37 hD321 hI5 hA21 h56 hD310 hD391 hI4
  have h1376 : Lem1376Full :=
    lem1376Full_holds hF318 h36 h37 h38 h139 h13314 h13315 h1356two h1337
  have h19 : Lem13819 := lem13819_of h16 h1376 h36c h139 h1334 h13 h13314 h13315 h1356two
  have hc : Case13820L24 :=
    case13820L24_of h36c h37 h38 h139 h1334 h1337 h13 h13314 h13315 h1356two
  have h20 : Lem13820 := lem13820_of h16 h36c h37 h38 h139 h1334 h13 hAut ha hb hc
  have hHat7 : Case13821Hat7 :=
    case13821Hat7_holds h16 h36c h36 h37 h38 hF318 h139 h1334 h13 hD310 hD391 hI4
  have hM22 : Case13821M22 := case13821M22_holds mathieuSmallIrr22_holds hA21 h56
    H.Mathieu.H16Pf.stmtH16_2_1M22_holds h16 h36c h36 h37 h38 hF318 h139 h1334 h13 hD310 hD391
    hI4
  have hL32 : Case13821L32 :=
    case13821L32_of hL32Hat h16 h36c h37 h38 h139 h1334 h13 hA21 hD310 hD391 hI4
  have h21 : Lem13821 := lem13821_of_cases h16 h36c h36 h37 h38 hF318 h139 h1334 h13 hD310 hD391
    hI4 h19 h20 hHat6 hHat7 hM22 hHatM22 hL32
  exact lem13827G2_of h21 h16 h36c h139 h1334 h13 h13315 h1356two h13314

theorem stmt13_8_1_of_root5gW_A5
    (h331 : CFSG.Quasithin.H13.Stmt3_3_1) (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2)
    (h12213 : CFSG.Quasithin.H13.Stmt12_2_13) (h13315 : Stmt13_3_15)
    (h523 : CFSG.Quasithin.H13.Stmt5_2_3) (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    (hcorr : CFSG.Quasithin.MS93.C134Weak)
    (hC137 : CFSG.Quasithin.H13.U3.GC137.C137StatementFiveSQTK)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5)
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW)
    (h13316 : Stmt13_3_16) (h1341 : Stmt13_4_1) (hK : Input13721K) (h28 : Input13828Six)
    (hAut : Fact13820Aut)
    (hHat6 : Case13821Hat6) (hHatM22 : Case13821HatM22) (hL32Hat : Case13821L32Hat) :
    Stmt13_8_1 :=
  have hZ437 : CFSG.Quasithin.H13.Ch4.Gap437Sp4Z :=
    CFSG.Quasithin.H13.Ch4.gap437Sp4Z_of CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds
      (CFSG.Quasithin.H13.Ch4.lemmaC53C56Six_of CFSG.Quasithin.theoremC126_proved
        CFSG.Quasithin.C58NS.minParabolicBlockSubnormal_holds)
      CFSG.Quasithin.a37ForSQTK_proved CFSG.Quasithin.a38ForSQTK_proved
      CFSG.Quasithin.a39ForSQTK_proved
  have h48 : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC48Statement G := fun _ _ _ =>
    CFSG.Quasithin.C48.asc48Statement_of_kw
      (CFSG.Quasithin.C41Pf.burnsideC41w_asc41Statement_of_big
        (CFSG.Quasithin.asc27Statement_of_c132 hC132 _) hcorr.big)
      (CFSG.Quasithin.asc27Statement_of_c132 hC132 _) hKW
      CFSG.Quasithin.C48Cover.c48SporCoverFact_holds
  stmt13_8_1_of_root5fW_A5 h331 h1332 h1222 h12213 h13315 h523 hC132 hcorr hC137 hA5 hKW h13316
    h1341 hK h28 hAut hHat6 hHatM22 hL32Hat
    (lem13827G2_of_root5W_A5 h331 h1332 h1222 h12213 h13315 h523 hC132 hcorr hC137 hA5 h48 hZ437
      hAut hHat6 hHatM22 hL32Hat)

end CFSG.Quasithin.H13.A6

end
