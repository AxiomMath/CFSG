module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4RepFin
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma6
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Am
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Case2
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Case3
public import CFSG.Quasithin.Vol2.Ch3D310Holds
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4InspFin
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma8Five
public import CFSG.Quasithin.Vol2.KGFactOut
public import CFSG.Quasithin.Vol2.KGFact1295
public import CFSG.Quasithin.Vol2.KGFact1297
public import CFSG.Quasithin.Vol2.Ch12Sec9Producer

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem linear_selected_natural_configuration_producer_of_inputs
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (helim125 : Elim125) (helim126 : Elim126)
    (h1293 : Lemma12_9_3K1) (h12hat : Lemma12_8_12_hat) (h13six : Lemma12_8_13_six_hat)
    (hSeven : G112ConclSeven) (hDI : Case1294FiveDI) (h331 : Stmt3_3_1) (hB69 : B69One)
    (hI4 : Insp4) (hFine : F918Fine4)
    (hS3 : S3OvergroupFact) :
    LinearSelectedNaturalConfigurationProducer := by
  have hD310 : D310 := d310_holds
  have hD391 : D391 := d391L_of_deep (d391Deep_of_inputs
      (d35_of_inputs asB42_holds B5.asB51_holds asB56_holds asA21SQTKSection asA36NoOddCover_holds
          (d35InspTwo_of_B51 B5.asB51_holds) d35InspSum_holds
          (d35InspUniq_of_chk (d35InspUniq8_of_chk d35ValChk_run) d35Chk_run)
          (d35InspB42_of_orbit asA21SQTKSection (F918X.d35InspOrbit_proved asA21SQTKSection)))
      B5.asB51_holds asA21SQTKSection)
  have h37 : A37ForSQTK := a37ForSQTK_of_cat QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat (QuasithinUnique.Vol2Native.a38ForSQTKCat_of_facts
    CFSG.Quasithin.mult2Fact QuasithinUnique.Vol2Native.a134SQTKFactCat
    QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
  have h39 : A39ForSQTK := a39ForSQTK_of_cat QuasithinUnique.Vol2Native.a39ForSQTKCat_proved
  have h5 := lemma12_8_8_five_of h1222 h12213 h37 h38 h39 outFact1295_holds
  have h1294 := lemma12_9_4_of h1222 h12213 h5 h1293 h12hat h13six (g112Inspect1294_of hSeven)
    (case1294Five_of_DI h1222 h12213 hDI)
  have h1295 := lemma12_9_5_of h1222 h12213 h37 h38 h39 h1293 h1294 outFact1295_holds
    (case1295Amalgam_of h1222 h37 h38 h39 h331 hB69)
    (case1295Two_of h1222 h37 h38 h39 hD310 hD391 hI4 hFine)
    (case1295Three_of h1222 h37 h38 parabolicFact1295_holds)
  have h1296 := lemma12_9_6_of h1222 h37 h38 h39 h1295 parabolicFact1296_holds
  have hcl := claim12_9_7_of_core h1222 h12213 h37 h38 h39 h1295 outFact1297_holds
    (core1297_of h1222 h37 h38 h39 h1295 h1296 latticeFact1297_holds)
  have h1297 := lemma12_9_7_of_claim h1222 hcl
  have h1299 := lemma12_9_9 h1222 h12213 h37 h38 h39 (lemma12_9_3_one h1222 h37 h38 h39) h1294
    h1295 h1296 h1297
  exact linear_selected_natural_configuration_producer_of_12_2_13 h1222 h12213
      (stmt12_5_1_of_elim125 h1222 helim125) (stmt12_6_34_of_elim126 h1222 helim126) h37 h38 h39
      h1294 (lemma12_9_7_of_claim h1222 hcl) h1299 (final1291_of h1222 h37 h38 h1295 hS3)

end CFSG.Quasithin.H13
