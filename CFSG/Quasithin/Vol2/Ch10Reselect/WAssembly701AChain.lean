module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Assembly701A
public import CFSG.Quasithin.Vol2.Ch3T326GF
public import CFSG.Quasithin.Background.Asc81cPfMain
public import CFSG.Quasithin.Background.E6TwentyThreePG
public import CFSG.Quasithin.Vol2.Ch7Prop711
public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalMain
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Holds
public import CFSG.Quasithin.Background.E6ThreeOpenHeX
public import CFSG.Quasithin.Vol2.Ch7Lem732
public import CFSG.Quasithin.Vol2.Ch8Input812Proved
public import CFSG.Quasithin.Background.E6ParabolicTorus
public import CFSG.Quasithin.Background.C24PfF
public import CFSG.Quasithin.Background.Asc82Holds
public import CFSG.Quasithin.Vol2.Ch7WAssembly701
public import CFSG.Quasithin.Vol2.Ch3T326H2

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.QuasithinUnique

theorem stmt7_0_1A_of_rowsW
    (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1) (h4414 : Stmt4_4_14) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h325 : Stmt3_2_5)
    (hshape : Stmt7_0_1_shapeC) (hM22 : Stmt7_2_1_M22Hat)
    (h755 : Input7_5_5) (h612 : ASInputs.AS_E_6_12) (h443 : Stmt4_4_3Orbit')
    (kf1 : OutTwoNilpotentFact) (hspor : KG68.SporadicSylowCenterCyclic)
    (hD4 : KG68.TrialityTwoSylowCenterCyclic) (hTits : KG68.TitsSylowCenterCyclic)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC24a : ∀ (G : Type) [Group G] [Finite G], ASC24One G)
    (hMS : C134L32CorrM)
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h8213 : Stmt8_2_13_cocode) (h8214 : Stmt8_2_14) (h831 : Stmt8_3_1)
    (h316 : Theorem316Statement) (h9A : Stmt9_omegaPlusA) : Stmt7_0_1A :=
  have h104 : CFSG.Quasithin.Asc81c.Thm104 := CFSG.Quasithin.Asc81c.Pf.thm104
  have hInsp : CFSG.Quasithin.E6.E623A6Insp := CFSG.Quasithin.E6.e623A6Insp_holds
  have h63 : ASInputs.AS_E_6_3 := CFSG.Quasithin.E6.as_E_6_3_of_thm104_insp h104 hInsp
  have h326 : Stmt3_2_6C := T326.stmt3_2_6C_of_stmt331 h331
  have h36 : A36ForSQTK := VolI.a36ForSQTK_holds
  have h37c : Vol2Native.A37ForSQTKCat := Vol2Native.a37ForSQTKCat_proved
  have h37 : A37ForSQTK := a37ForSQTK_of_cat h37c
  have h38c : Vol2Native.A38ForSQTKCat :=
    Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved h37c
  have h38 : A38ForSQTK := a38ForSQTK_of_cat h38c
  have h39c : Vol2Native.A39ForSQTKCat := Vol2Native.a39ForSQTKCat_proved
  have h39 : A39ForSQTK := a39ForSQTK_of_cat h39c
  have h3228 : Stmt3_2_2_eight := stmt3_2_2_eight_proved
  have h3104 : Stmt3_2_10_four := stmt3_2_10_four_holds h38c h39c
  have h3108 : Stmt3_2_10_eight := stmt3_2_10_eight_holds h38c h39c
  have h329 : Stmt3_2_9C := stmt3_2_9C_of h325 h316
  have h711 : Stmt7_1_1 := Prop711.stmt7_1_1_of h325 (stmt3_2_6Lt_of_C h326) h329 h331 hC58 h317
    h37 h38 h39 h3228
  have h711n : Stmt7_1_1_normal := stmt7_1_1_normal_holds h37 h38
  have hC24b : ∀ (G : Type) [Group G] [Finite G], ASC24TwoChar G :=
    fun _ _ _ => C24Pf.asc24TwoChar_of asc82Thm2_holds h37 h38
  have h36c : Vol2Native.A36CoreForSQTKCat := Vol2Native.a36CoreForSQTKCat_proved
  have hA23 : A23FourCentralFact :=
    a23FourCentralFact_of (a23NoncyclicCenterFact_of (KG68.a23CyclicCenterFact_of hspor hD4 hTits)
      KG68.a23SmallTwoRankFact_holds) NQCat.LieCentral.lieCentralIndexFact_holds
  have h773 : Stmt7_7_3 := Sec77.stmt7_7_3_ofW h37 h38 h39 h3228 h711n h325 h3104 h3108 h443
    h37c h38c h36c h36 h755 kf1 a23SQTKListFact hA23
    (NQCat.LieMult.lieMultiplierFact_of NQCat.LieMult.l34NoCentralE16_holds
        NQCat.LieMult.g24NoCentralE16_holds NQCat.LieMult.sz8NoCentralE16_holds) NQCat.LieCartan.lieCartanFact_holds
    NQCat.LieThompson.lieThompsonFact_holds asB56_holds hC27 hC24a hC24b
    (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) factA318Excl_holds
    sp4PlaneFixFact_holds B5.asB51_holds asI16Cover_of asI16CoverA8_of hMS
  have h771 : Stmt7_7_1 :=
    stmt7_7_1_of h37 h38 h39 (stmtFSUModule_of_eight h3228) h711n h325 h3228 h612 h773
  have hin : Input8_1_2 :=
    input8_1_2_of (CFSG.Quasithin.E6.parabolicTorusFact_of_e22C hE22 e22TorusFacts_holds)
      (stmt7_3_2_of h37 h38 h39 h3228 h325 h63 h711 h711n h771 stmt7_2_1_Sp4Pair stmt7_2_1_S7
          stmt7_2_1_m_Sz stmt7_2_1_m_L3Nine stmt7_2_1_m_Mathieu stmt7_2_1_m_SL3Pair
          stmt7_2_1_m_L3Wreath) h325 h443
  have h701 : Stmt7_0_1 :=
    stmt7_0_1_of_rowsW hE22 h331 h4414 hC58 h317 h325 h326 h63 hin h711 h711n hshape hM22 h755 h612
      h443 kf1 hspor hD4 hTits hC27 hC24a hC24b hMS hC48 h8213 h8214 h831
      (stmt9_omegaPlus_of_A h9A)
  stmt7_0_1A_of_C h701 h326 h9A

end CFSG.Quasithin.H13.Ch9
