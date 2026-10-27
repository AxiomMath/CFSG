module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310Z
public import CFSG.Quasithin.Vol2.Ch8Sec3Reduce
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8312C
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem839
public import CFSG.Quasithin.Vol2.KGFact838
public import CFSG.Quasithin.H13.NQCatRkOneHolds
public import CFSG.Quasithin.Background.E6ParabolicTorus
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop3210Ch7
public import CFSG.Quasithin.EmptyFaithful.S146zMList
public import CFSG.Quasithin.EmptyFaithful.S152HeProp134
public import CFSG.Quasithin.Vol2.GoldschmidtC58Proved
public import CFSG.Quasithin.Vol2.GoldschmidtTD317
public import CFSG.Quasithin.Vol2.GoldschmidtCor332
public import CFSG.Quasithin.H13.E22CHolds
public import CFSG.Quasithin.Vol2.GoldschmidtClaim8310NAut
public import CFSG.Quasithin.Background.E6ThreeOpenHeX
public import CFSG.Quasithin.Background.E6TwentyThreePG

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique

theorem stmt8_3_10_of_frontier
    (h104 : Asc81c.Thm104) (h443 : Stmt4_4_3Orbit') (h326 : Stmt3_2_6C) (h734 : Stmt7_3_4) :
    Stmt8_3_10 :=
  have h63 : ASInputs.AS_E_6_3 := E6.as_E_6_3_of_thm104_insp h104 E6.e623A6Insp_holds
  have h37 := Vol2Native.a37ForSQTKCat_proved
  have h38 := Vol2.Ch10.SecA.a38ForSQTKCat_proved
  have h39 := Vol2Native.a39ForSQTKCat_proved
  have h3228 := stmt3_2_2_eight_proved
  have hmod := stmtFSUModule_of_eight h3228
  have h3108 := stmt3_2_10_eight_holds h38 h39
  have hNoN := e22StatementNoN_proved
  have h832 := stmt8_3_2_of h63
  have h835 := stmt8_3_5_of hmod input7_0_2_unique_proved input8_3_Q_proved h832
  have h836 := stmt8_3_6_of hmod h832 h835
  have h837 := stmt8_3_7_of_torus Vol2Native.a36ForSQTKCat_proved h37 h38 h39 sqtkList3Dvd_proved
    h3228 theoremC58_proved as317Sylow_proved Cor332.stmt3_3_2MTwo_holds h326 h3108
    prop134E9He_holds h734 h836 KG838.kg838Out_holds NQCat.RkOne.kgRankOneOvergroups_holds hNoN h443
  have h838 := stmt8_3_8_of_lie h37 h38 h39 h3228 theoremC58_proved as317Sylow_proved hmod h326
    h3108 h836 h837 KG838.kg838Out_holds KG838.kg838Par_holds hNoN h443
  stmt8_3_10_of_kg e22StatementC_holds h443 h37 h38 h39 h3228
    theoremC58_proved as317Sylow_proved Cor332.stmt3_3_2MTwo_holds h326 h3108 h832 h835 h837
    (stmt8_3_9_of hmod input7_0_2_unique_proved h832 h734 h838)
    (claim8310Gz_of h37 h38 h39 h3228 h326 h837 KG838.kg838Out_holds)
    (claim8310N_of' h37)

theorem stmt8_3_1_of_frontier
    (h104 : Asc81c.Thm104) (h443 : Stmt4_4_3Orbit') (h326 : Stmt3_2_6C) (h327 : Stmt3_2_7C)
    (h734 : Stmt7_3_4) : Stmt8_3_1 :=
  have h63 : ASInputs.AS_E_6_3 := E6.as_E_6_3_of_thm104_insp h104 E6.e623A6Insp_holds
  have h37 := Vol2Native.a37ForSQTKCat_proved
  have h38 := Vol2.Ch10.SecA.a38ForSQTKCat_proved
  have h39 := Vol2Native.a39ForSQTKCat_proved
  have h3228 := stmt3_2_2_eight_proved
  have hmod := stmtFSUModule_of_eight h3228
  have h3108 := stmt3_2_10_eight_holds h38 h39
  have hNoN := e22StatementNoN_proved
  have h832 := stmt8_3_2_of h63
  have h836 := stmt8_3_6_of hmod h832
    (stmt8_3_5_of hmod input7_0_2_unique_proved input8_3_Q_proved h832)
  have h837 := stmt8_3_7_of_torus Vol2Native.a36ForSQTKCat_proved h37 h38 h39 sqtkList3Dvd_proved
    h3228 theoremC58_proved as317Sylow_proved Cor332.stmt3_3_2MTwo_holds h326 h3108
    prop134E9He_holds h734 h836 KG838.kg838Out_holds NQCat.RkOne.kgRankOneOvergroups_holds hNoN h443
  have h838 := stmt8_3_8_of_lie h37 h38 h39 h3228 theoremC58_proved as317Sylow_proved hmod h326
    h3108 h836 h837 KG838.kg838Out_holds KG838.kg838Par_holds hNoN h443
  have h8310 := stmt8_3_10_of_frontier h104 h443 h326 h734
  have hPT := E6.parabolicTorusFact_of_e22C e22StatementC_holds
    e22TorusFacts_holds
  stmt8_3_1_of_8310_8314 h63 h8310
    (stmt8_3_14_of hmod
      (stmt8_3_11_of h3228 (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
        (a39ForSQTK_of_cat h39) h326 hPT h832 h838 h8310)
      (stmt8_3_13_of (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38) (a39ForSQTK_of_cat h39)
        hmod h326 (stmt3_2_10_four_holds h38 h39) (stmt3_2_10_six_of_stmt3_2_7C
          (stmt3_2_3_of_a38_a39 h38 h39) stmt3_2_2_eight_proved h327)
        (stmt8_3_12_of h37 h38 h3228 h326 h8310)))

end CFSG.Quasithin.H13
