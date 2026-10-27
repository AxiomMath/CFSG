module

public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.H13.A6S13821zz17
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.Quasithin.H13.A6S1356S6Fr
public import CFSG.Quasithin.H13.A6S1356S6Q
public import CFSG.Quasithin.H13.A6S13813m
public import CFSG.Quasithin.H13.GoldschmidtL1328Nat
public import CFSG.Quasithin.H13.U3L134W
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8
public import CFSG.Quasithin.Vol2.Ch3D310Holds
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem323
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

theorem case13820a_holds
    (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) :
    Case13820a := by
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
  have hA21 : AsA21SQTKSection := asA21SQTKSection
  have hF318 : A318Facts := a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds
  have hB42 := CFSG.Quasithin.asB42_holds
  have hB45 := CFSG.Quasithin.asB45_holds
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
  have hF10 := CFSG.Quasithin.Vol2.Ch10.SecA.facts10_1_holds
  have h323 : Stmt3_2_3 := stmt3_2_3_of h37c h38c h39c
  have h1226 : Stmt12_2_6 := stmt12_2_6_of h1222 h323
  have h1228 : Stmt12_2_8 := stmt12_2_8_of h1222 hF318 h38
  have h139 : Stmt13_3_9 :=
    U3.stmt13_3_9_of_1332 h1332 h1226 h1228 (U3.stmt13_2_2_9L1_holds h1332)
  have h1334 : Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have h1337 : Stmt13_3_7 := U3.stmt13_3_7_of h1332 h1228
  have h13 : Lem13813 := lem13813_holds h13314 h13315 h1356two h139
  exact case13820a_of h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hA21 hB42 hF10 h1337 h13314
    h13315 h1356two B5.asB51_holds

end CFSG.Quasithin.H13.A6
