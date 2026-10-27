module

public import CFSG.Quasithin.Vol2.Ch7Assembly771
public import CFSG.Quasithin.Vol2.Ch7Lem734Asm
public import CFSG.Quasithin.Vol2.Ch7Stmt721M12
public import CFSG.Quasithin.Vol2.Ch7Stmt721M23Code
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop3210Ch7
public import CFSG.Quasithin.Vol2.Ch8InputsProved
public import CFSG.Quasithin.Vol2.Ch7Sec77InputsSplit
public import CFSG.Quasithin.Vol2.Ch7Sec77LieSp4
public import CFSG.Quasithin.H13.KGFactA23Cyclic
public import CFSG.Quasithin.H13.KGFactA23Small
public import CFSG.Quasithin.H13.NQCatLieCentralHolds
public import CFSG.Quasithin.H13.NQCatLieMultSz8
public import CFSG.Quasithin.H13.NQCatLieCartanHolds
public import CFSG.Quasithin.H13.NQCatLieThompsonHolds
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.Background.F918F3
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Vol2.Ch7WProp773

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique

theorem stmt7_0_1_of_rowsW
    (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1) (h4414 : Stmt4_4_14) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h325 : Stmt3_2_5) (h326 : Stmt3_2_6C) (h63 : ASInputs.AS_E_6_3)
    (hin : Input8_1_2) (h711 : Stmt7_1_1) (h711n : Stmt7_1_1_normal)
    (hshape : Stmt7_0_1_shapeC) (hM22 : Stmt7_2_1_M22Hat)
    (h755 : Input7_5_5) (h612 : ASInputs.AS_E_6_12) (h443 : Stmt4_4_3Orbit')
    (kf1 : OutTwoNilpotentFact) (hspor : KG68.SporadicSylowCenterCyclic)
    (hD4 : KG68.TrialityTwoSylowCenterCyclic) (hTits : KG68.TitsSylowCenterCyclic)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC24a : ∀ (G : Type) [Group G] [Finite G], ASC24One G)
    (hC24b : ∀ (G : Type) [Group G] [Finite G], ASC24TwoChar G) (hMS : C134L32CorrM)
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h8213 : Stmt8_2_13_cocode) (h8214 : Stmt8_2_14) (h831 : Stmt8_3_1)
    (h9 : Stmt9_omegaPlus) : Stmt7_0_1 :=
  have h37 : A37ForSQTK := a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved
  have h38c : Vol2Native.A38ForSQTKCat :=
    Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat h38c
  have h39c : Vol2Native.A39ForSQTKCat := Vol2Native.a39ForSQTKCat_proved
  have h39 : A39ForSQTK := a39ForSQTK_of_cat h39c
  have h3228 : Stmt3_2_2_eight := stmt3_2_2_eight_proved
  have hmod : StmtFSUModule := stmtFSUModule_of_eight h3228
  have h3104 : Stmt3_2_10_four := stmt3_2_10_four_holds h38c h39c
  have h3108 : Stmt3_2_10_eight := stmt3_2_10_eight_holds h38c h39c
  have h36c : Vol2Native.A36CoreForSQTKCat := Vol2Native.a36CoreForSQTKCat_proved
  have h36 : A36ForSQTK := VolI.a36ForSQTK_holds
  have hA23 : A23FourCentralFact :=
    a23FourCentralFact_of (a23NoncyclicCenterFact_of (KG68.a23CyclicCenterFact_of hspor hD4 hTits)
      KG68.a23SmallTwoRankFact_holds) NQCat.LieCentral.lieCentralIndexFact_holds
  have h772 : Stmt7_7_2 := Sec77.stmt7_7_2_of h37 h38 h39 h3228 h711n h325 h3104 h3108 h443
    Vol2Native.a37ForSQTKCat_proved h38c h755 kf1 a23SQTKListFact hA23
    (NQCat.LieMult.lieMultiplierFact_of NQCat.LieMult.l34NoCentralE16_holds
        NQCat.LieMult.g24NoCentralE16_holds NQCat.LieMult.sz8NoCentralE16_holds) NQCat.LieCartan.lieCartanFact_holds
    NQCat.LieThompson.lieThompsonFact_holds
  have h773 : Stmt7_7_3 := Sec77.stmt7_7_3_ofW h37 h38 h39 h3228 h711n h325 h3104 h3108 h443
    Vol2Native.a37ForSQTKCat_proved h38c h36c h36 h755 kf1 a23SQTKListFact hA23
    (NQCat.LieMult.lieMultiplierFact_of NQCat.LieMult.l34NoCentralE16_holds
        NQCat.LieMult.g24NoCentralE16_holds NQCat.LieMult.sz8NoCentralE16_holds) NQCat.LieCartan.lieCartanFact_holds
    NQCat.LieThompson.lieThompsonFact_holds asB56_holds hC27 hC24a hC24b
    (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) factA318Excl_holds
    sp4PlaneFixFact_holds B5.asB51_holds asI16Cover_of asI16CoverA8_of hMS
  have h771 : Stmt7_7_1 := stmt7_7_1_of h37 h38 h39 hmod h711n h325 h3228 h612 h773
  have h734 : Stmt7_3_4 := stmt7_3_4_of_rows hE22 h331 h4414 hC58 h317 h325 h63 hin h711
    h711n h771
  stmt7_0_1_of_inputs_771 h37 h38 h39 hshape h711 h711n h325 h3228 h734 hM22
    stmt7_2_1_M12 stmt7_2_1_M23Code hin h755 h63 h612 h773 h772 h3104
    (stmt3_2_10_six_of_stmt3_2_7C (stmt3_2_3_of_a38_a39 h38c h39c) stmt3_2_2_eight_proved
      (stmt3_2_7C_of h325 h326))
    (stmt8_1_3_M24_final_q hC48 h711n h325 hin h734) h8213 h8214 h831 h9

end CFSG.Quasithin.H13
