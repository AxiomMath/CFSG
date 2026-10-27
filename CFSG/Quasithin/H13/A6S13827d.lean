module

public import CFSG.Quasithin.H13.A6S138Ext3
public import CFSG.Quasithin.H13.A5Close1321c
public import CFSG.Quasithin.H13.GoldschmidtA6RowsCentG2
public import CFSG.Quasithin.H13.GoldschmidtA6RowsA6
public import CFSG.Quasithin.H13.GoldschmidtA6RowsA8
public import CFSG.Quasithin.H13.A6S138Id
public import CFSG.Quasithin.H13.A6S13821x
public import CFSG.Quasithin.H13.A6S13821i
public import CFSG.Quasithin.H13.A6S13821k
public import CFSG.Quasithin.H13.A6S13821o
public import CFSG.Quasithin.H13.A6S13825nh
public import CFSG.Quasithin.H13.A6S13826m
public import CFSG.Quasithin.H13.A6S13813m
public import CFSG.Quasithin.H13.A6S13816v
public import CFSG.Quasithin.H13.A6S1372L76N3o
public import CFSG.Quasithin.Background.F918D36Holds
public import CFSG.Quasithin.Background.H16TwoM22PfD
public import CFSG.Quasithin.EmptyFaithful.S153ILemma122
public import CFSG.Quasithin.H13.GoldschmidtL1328Nat
public import CFSG.Quasithin.H13.U3L134W
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8
public import CFSG.Quasithin.H13.A6S13821zg
public import CFSG.Quasithin.H13.A6S13824v
public import CFSG.Quasithin.H13.U3L14Open
public import CFSG.Quasithin.Vol2.Ch3D310Holds
public import CFSG.Quasithin.Background.F918J6
public import CFSG.Quasithin.Background.F918K8
public import CFSG.Quasithin.Background.F918V3Main
public import CFSG.Quasithin.Background.F918V3SZMain
public import CFSG.Quasithin.Background.F918Z8Fin

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

theorem input13827Six_of_root5b
    (h331 : CFSG.Quasithin.H13.Stmt3_3_1) (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2)
    (h12213 : CFSG.Quasithin.H13.Stmt12_2_13) (h13315 : Stmt13_3_15)
    (h523 : CFSG.Quasithin.H13.Stmt5_2_3)
    (hC137 : CFSG.Quasithin.H13.U3.GC137.C137StatementFiveSQTK)
    (hRes : CFSG.Quasithin.H13.A5.Res1328a)
    (hRest : CFSG.Quasithin.H13.A5.Rest1327)
    (hU3K : CFSG.Quasithin.H13.U3.U3LineComponentExclusion)
    (hAut : Fact13820Aut) (ha : Case13820a) (hb : Case13820bSL34U38)
    (hHat6 : Case13821Hat6) (hHatM22 : Case13821HatM22) (hL32Hat : Case13821L32Hat)
    (hG2 : Lem13827G2) : Input13827Six := by
  have h13314 : Stmt13_3_14 := U3.stmt13_3_14_of_open (h_Stmt3_3_1 := h331)
    (h_Stmt12_2_2 := h1222) (h_Stmt12_2_13 := h12213) (h_Stmt13_3_2 := h1332)
    (h_C137StatementFiveSQTK := hC137) (h_Stmt5_2_3 := h523) (h_Res1328a := hRes)
    (h_Rest1327 := hRest) (h_U3LineComponentExclusion := hU3K)
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
  have h39 : A39ForSQTK := a39ForSQTK_of_cat h39c
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
  have h24 : Lem13824 :=
    lem13824_holds' h1376 h21 h16 h36c h139 h1334 h13 h13314 h13315 h1356two h1337
  have h18 : Lem13818Four := lem13818Four_holds h36c h139 h1334 h13 h13314 h13315 h1356two
  have h25 : Lem13825 :=
    lem13825_of (lem13825One_of h21 h16 h1376 (G64.lemmaG64_of_b5 h56))
        (lem13825NoL3_of h21 h16 h1334) (lem13825Par_of h21 h16 h1334)
        (lem13825G1_of h37 h39 h16 h21) (lem13825NoA6_of h21 h16 h1334 h18)
        (lem13825Nat_of hA21 h21 h16 h1334 h18)
  have h26 : Lem13826 := lem13826_of h1376 h21 h16 h36c h139 h1334 h13 h13314 h13315 h1356two
  exact input13827Six_of_leaves h13315 h1356two h13 h16 h21 h24 h25 h26 hG2

theorem stmt13_8_1_of_root5b
    (h331 : CFSG.Quasithin.H13.Stmt3_3_1) (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2)
    (h12213 : CFSG.Quasithin.H13.Stmt12_2_13) (h13315 : Stmt13_3_15)
    (h523 : CFSG.Quasithin.H13.Stmt5_2_3)
    (hC137 : CFSG.Quasithin.H13.U3.GC137.C137StatementFiveSQTK)
    (hRes : CFSG.Quasithin.H13.A5.Res1328a)
    (hRest : CFSG.Quasithin.H13.A5.Rest1327)
    (hU3K : CFSG.Quasithin.H13.U3.U3LineComponentExclusion)
    (h13316 : Stmt13_3_16) (h1341 : Stmt13_4_1) (hctk : Input13515CTK) (hU43 : StmtU43Type)
    (hK : Input13721K) (h28 : Input13828Six)
    (hAut : Fact13820Aut) (ha : Case13820a) (hb : Case13820bSL34U38)
    (hHat6 : Case13821Hat6) (hHatM22 : Case13821HatM22) (hL32Hat : Case13821L32Hat)
    (hG2 : Lem13827G2) : Stmt13_8_1 := by
  have h13314 : Stmt13_3_14 := U3.stmt13_3_14_of_open (h_Stmt3_3_1 := h331)
    (h_Stmt12_2_2 := h1222) (h_Stmt12_2_13 := h12213) (h_Stmt13_3_2 := h1332)
    (h_C137StatementFiveSQTK := hC137) (h_Stmt5_2_3 := h523) (h_Res1328a := hRes)
    (h_Rest1327 := hRest) (h_U3LineComponentExclusion := hU3K)
  have h1336 := U3.stmt13_3_6_of_1332 h1332 h1222 h12213 h331
    (A5.stmt13_2_7_ofNoN h331 h523 h1222 e22StatementNoN_proved hRes hRest)
  exact stmt13_8_1_of_ext3 h1332 h13316 h1341 h1336 h13315 h1222 hctk hU43
      (A5.facts1321_of_b45 asB45_holds) A5.factRankRows1321 A5.factA7Grp1321 A5.factL3Grp1321
      A5.factOutRows1321 factCentG2 factCommA6 factCommA8 factCommG2 h13314 hK factAutA6Rank_holds
      (input13827Six_of_root5b h331 h1332 h1222 h12213 h13315 h523 hC137 hRes hRest hU3K hAut ha hb
          hHat6 hHatM22 hL32Hat hG2) h28

end CFSG.Quasithin.H13.A6
