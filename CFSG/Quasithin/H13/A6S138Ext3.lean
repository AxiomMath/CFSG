module

public import CFSG.Quasithin.H13.A6S1514G248
public import CFSG.Quasithin.H13.A6S13721b
public import CFSG.Quasithin.H13.A6S1356S6Fr
public import CFSG.Quasithin.H13.A6Rows1321
public import CFSG.Quasithin.H13.A6S13833m
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Quasithin.H13.A6S1356S6Q
public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.H13.GoldschmidtG52Main

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt13_8_1_of_ext3
    (h1332 : Stmt13_3_2) (h13316 : Stmt13_3_16) (h1341 : Stmt13_4_1) (h1336 : Stmt13_3_6)
    (h13315 : Stmt13_3_15) (h1222 : Stmt12_2_2) (hctk : Input13515CTK) (hU43 : StmtU43Type)
    (hF : A5.Facts1321) (hR : A5.FactRankRows1321) (hA7 : A5.FactA7Grp1321)
    (hL3 : A5.FactL3Grp1321) (hO : A5.FactOutRows1321) (hCG2 : FactCentG2) (hc6 : FactCommA6)
    (hc8 : FactCommA8) (hcG2 : FactCommG2) (h13314 : Stmt13_3_14) (hK : Input13721K)
    (hA6 : FactAutA6Rank) (h27 : Input13827Six) (h28 : Input13828Six) : Stmt13_8_1 :=
  have hC124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G) :=
    C124.c124StatementSQTK_of_e22 e22StatementNoN_proved
  have hG52 : StmtG52 := G52.stmtG52_holds
  have hB : Input1356TwoS6Block := input1356TwoS6Block_of h13315
  have h1356two : Input1356Two :=
    input1356Two_of h1222 (input1356TwoS6_of_sqtk hC124 h1222 hB)
  have h38 : A38ForSQTK := a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact
    Vol2Native.a134SQTKFactCat Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
  stmt13_8_1_of_inputs h1332 h13316
    (stmt13_7_8_of_inputs h1332 h13316 h1341
      (stmt13_5_12_six_of_13521 h1332 h13316 h1341 h13315 h1356two
        (obl13_5_14Six_of_1356 h13315 h1356two) hctk hU43 h38 hF hR hA7 hL3 hO
        (input13521Four_of_cent h13315 h1356two h38 hF hR hA7 hL3 hO
          (factCentRows1321_of factCentA6 factCentA8 hCG2))
        (input13521Six_of_comm h13315 h1356two h38 hF hR hA7 hL3 hO
          (factCommRows1321_of hc6 hc8 hcG2)))
      h13315 h1356two
      (input1379Six_of h13315 h1356two h13314 (input13721Six_of h13315 h1356two h13314 hK hA6)))
    (stmt13_8_3_34_of_inputs h1332 h13316 h1341 h1336 h13315 h1356two
      (input1384Six_of h27 h28
        (input13833Six_of h13315 h1356two h13314 (input13833Ab_of h13315 h1356two h13314 hG52
          (input13833AbCover_holds h13315 h1356two h13314 hG52)))
        (input13834Six_of h13315 h1356two h13314
          (lemma13834Six_of h13315 h1356two h13314
            (lemma13834SixOneTwo_holds h13315 h1356two h13314)))))

end CFSG.Quasithin.H13.A6
