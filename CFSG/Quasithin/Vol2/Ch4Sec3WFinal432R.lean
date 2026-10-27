module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.Vol2.Ch3xC58NSMPB
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Mult
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Vol2.Ch11SecB414Z
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Holds
public import CFSG.Quasithin.Vol2.KGFactInsp4316
public import CFSG.Quasithin.Vol2.KGFactInspOutDer
public import CFSG.Quasithin.Vol2.KGFactInspE16m
public import CFSG.Quasithin.Vol2.KGFactInspE16L
public import CFSG.Quasithin.Vol2.KGFactInspExc
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspG2
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspD4
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspF4
public import CFSG.Quasithin.Vol2.Ch4Sec3WFinal432U

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt4_3_2_of_restW
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) (hM2223 : Insp436M22M23)
    (h134 : MS93.burnsideC134w_AS_C_1_34_corrBig) (hZ : Gap437Sp4Z) : Stmt4_3_2 :=
  stmt4_3_2_of_inputs_l4316W NQCat.l2RankOneSylowFact_holds theoremC126_proved
      C58NS.minParabolicBlockSubnormal_holds hC48 insp436G2_holds insp436D4_holds insp436F4_holds
      hM2223
      (sp4MultTrivial_of CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
      (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) asB56_holds
      B414.lemmaB414Corrected_holds
      (A38c14.a312ForSQTK_of_residual A3Facts.a134ForSQTK A3Facts.schreierSQTK
          A38c17.a312ResidualRest2_holds.toRest3.toRest4.toRest10.toRest) h134
      (KGInsp4316.insp4316_of KGInsp4316.insp4316OutDer_holds KGInsp4316.insp4316E16m_holds
          KGInsp4316.insp4316E16L_holds
          (KGInsp4316.insp4316L3eps_of KGInsp4316.insp4316L3epsOdd_holds)
          (KGInsp4316.insp4316OutLie_of KGInsp4316.insp4316OutLieOdd_holds
              (KGInsp4316.insp4316OutLieRank2_of KGInsp4316.insp4316OutLieExc_holds))) hZ

end CFSG.Quasithin.H13.Ch4
