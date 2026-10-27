module

public import CFSG.Quasithin.H13.GoldEdgeS3Holds
public import CFSG.Quasithin.H13.NQS134EW
public import CFSG.Quasithin.H13.GoldschmidtU3RankLFinal
public import CFSG.Quasithin.H13.GoldschmidtU3ThreeCase
public import CFSG.Quasithin.Background.E6TwelveProved
public import CFSG.Quasithin.H13.NQCatKG68All
public import CFSG.Quasithin.H13.GoldschmidtL1328Nat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.GoldschmidtC58Proved
public import CFSG.Quasithin.Vol2.GoldschmidtTD317

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt13_3_16_of_remaining
    (h1332 : Stmt13_3_2) (h12211 : Stmt12_2_11') (h1227 : Stmt12_2_7)
    (hA : U3.U3NondegLineCentralizer) (h13314 : A6.Stmt13_3_14) : Stmt13_3_16 :=
  U3.stmt13_3_16_of_inputs_l1312_of_1227 h1332 (theorem311Stmt_of_C58 theoremC58_proved)
      (CFSG.Quasithin.E6.as_E_6_12_proved KG68.e68ComponentFacts_holds) h12211
      U3.uniqueThreeCaseModelReduction_holds h1227 hA h13314

theorem stmt13_4_1_of_remaining
    (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) (h1228 : Stmt12_2_8)
    (h12213 : Stmt12_2_13) (h331 : Stmt3_3_1) (h1327 : A5.Stmt13_2_7)
    (hC137 : U3.C137StatementFiveZ)
    (hF : F6.TheoremF618Cat) (h12211 : Stmt12_2_11') (h1227 : Stmt12_2_7)
    (hA : U3.U3NondegLineCentralizer) (h13314 : A6.Stmt13_3_14) : A6.Stmt13_4_1 :=
  stmt13_4_1_assembled h1332 h1222 h1226 h1228 h12213 h331 h1327 (U3.stmt13_2_2_9L1_holds h1332)
      (U3.stmt13_3_16_of_inputs_l1312_of_1227 h1332 (theorem311Stmt_of_C58 theoremC58_proved)
          (CFSG.Quasithin.E6.as_E_6_12_proved KG68.e68ComponentFacts_holds) h12211
          U3.uniqueThreeCaseModelReduction_holds h1227 hA h13314) theoremC58_proved
      as317Sylow_proved asB56_holds hC137 goldschmidtEdgeBoundS3_holds hF
      Vol2Native.a37ForSQTKCat_proved Vol2Native.a39ForSQTKCat_proved

end CFSG.Quasithin.H13.NQS134
