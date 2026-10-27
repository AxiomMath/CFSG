module

public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.Background.Asc81cPfMain
public import CFSG.Quasithin.Background.E6ThreeOpenHeX
public import CFSG.Quasithin.Background.E6TwentyThreePG
public import CFSG.Quasithin.Background.F918Fine4Pf
public import CFSG.Quasithin.Background.G11FixHolds
public import CFSG.Quasithin.Background.E6TwelveProved
public import CFSG.Quasithin.H13.NQCatKG68All
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.H13.E22CHolds
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem9
public import CFSG.Quasithin.Vol2.Ch12Sec2Wired
public import CFSG.Quasithin.Vol2.Ch12Sec4Wired
public import CFSG.Quasithin.Vol2.Ch12Sec5ElimBad
public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Cert
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3L249
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3SL3
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4SevenSp
public import CFSG.Quasithin.Vol2.Ch12Sec9Skeleton
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139Holds
public import CFSG.Quasithin.Vol2.Ch3xD15Proved
public import CFSG.Quasithin.Vol2.GoldschmidtTD317
public import CFSG.Quasithin.Vol2.GoldschmidtTD32
public import CFSG.Quasithin.Vol2.GoldschmidtC58Proved

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem linear_selected_natural_configuration_producer_of_leaves
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h331 : Stmt3_3_1) (h1227 : Stmt12_2_7)
    (h12211 : Stmt12_2_11') (h1231 : Stmt12_3_1) (helim126 : Elim126)
    (hDI : Case1294FiveDI) :
    LinearSelectedNaturalConfigurationProducer :=
  have h37 : A37ForSQTK := a37ForSQTK_proved
  have h38 : A38ForSQTK := a38ForSQTK_proved
  have h39 : A39ForSQTK := a39ForSQTK_proved
  have h1228 : Stmt12_2_8 :=
    stmt12_2_8_of h1222 (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) h38
  have h1241 : Lemma12_4_1 := lemma12_4_1_of h331 h1222 stmt3_2_2_eight_proved h1227
    (cor12_3_2_of_stmt12_3_1 h1231 h1227 h1222)
  have helim125 : Elim125 := S125Bad.elim125
    (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds)
    (dynkinFact1293_of dynkinFact1293SL3_holds) h331 h1222 stmt3_2_3_proved
    (pre1242_of_stmts h331 h1222) stmt3_2_2_eight_proved h1228
    (stmt12_2_9_of h331 h1222 theoremC58_proved as317Sylow_proved) (stmt12_2_10_of_1222 h1222)
    h12211 h1241 asB42_holds (E6.as_E_6_3_of_thm104_insp Asc81c.Pf.thm104 E6.e623A6Insp_holds)
    (E6.as_E_6_12_proved H13.KG68.e68ComponentFacts_holds) e22StatementC_holds (E2.e22TorusCover_of_facts e22TorusFacts_holds)
    VolI.a36ForSQTK_holds h37 h38 h39 a312ForSQTK_proved
  linear_selected_natural_configuration_producer_of_inputs h1222 h12213 helim125 helim126
    (lemma12_9_3K1_of_inputs h1222 VolI.a36ForSQTK_holds h37 h38 h39 a312ForSQTK_proved
      (dynkinFact1293_of dynkinFact1293SL3_holds))
    (lemma12_8_12_hat_of h1222 h12213 G11.theoremG112Fix_holds)
    (lemma12_8_13_six_hat h1222 h12213 h1228 h37 h38 h39
      (lemma12_8_8_five_of h1222 h12213 h37 h38 h39 outFact1295_holds))
    g112ConclSeven_holds hDI h331 b69One_proved
    (insp4_of_inputs asA21SQTKSection factG2Cayley_holds asB42_holds asB45_holds d310_holds)
    (F918Fine4Pf.f918Fine4_of d310_holds (d391L_of_deep (d391Deep_of_inputs
        (d35_of_inputs asB42_holds B5.asB51_holds asB56_holds asA21SQTKSection asA36NoOddCover_holds
            (d35InspTwo_of_B51 B5.asB51_holds) d35InspSum_holds
            (d35InspUniq_of_chk (d35InspUniq8_of_chk d35ValChk_run) d35Chk_run)
            (d35InspB42_of_orbit asA21SQTKSection (F918X.d35InspOrbit_proved asA21SQTKSection)))
        B5.asB51_holds asA21SQTKSection))) s3OvergroupFact_holds

end CFSG.Quasithin.H13
