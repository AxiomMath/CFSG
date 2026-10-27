module

public import CFSG.Quasithin.H13.A7NatG10Owed
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin

theorem stmtA7NaturalModuleConfig_of_hubs
    (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1)
    (h1225 : Stmt12_2_5) (h12212 : Stmt12_2_12) (h12213 : Stmt12_2_13)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC111 : ∀ (G : Type) [Group G] [Finite G], ASC111Statement G)
    (hC19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G)
    (h1229 : Stmt12_2_9) (h3214 : Stmt3_2_14)
    (hC41 : ∀ (G : Type) [Group G] [Finite G], ASC41Statement G) (hF314 : A314Facts)
    (hList : QuasithinUnique.Vol2Native.A312ListFactsCat) :
    StmtA7NaturalModuleConfig :=
  stmtA7NaturalModuleConfig_of_owed h1222 h331 h1225 h12212 h12213 hC27
    VolI.asc129Statement_holds hC111 hC19
    (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) h1229 h3214 hC41
    asB56_holds B5.asB51_holds hF314 hList

theorem stmt12_3_1_of_hubs
    (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1)
    (h1225 : Stmt12_2_5) (h12212 : Stmt12_2_12) (h12213 : Stmt12_2_13)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC111 : ∀ (G : Type) [Group G] [Finite G], ASC111Statement G)
    (hC19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G)
    (h3214 : Stmt3_2_14) (hC41 : ∀ (G : Type) [Group G] [Finite G], ASC41Statement G)
    (hF314 : A314Facts) (hList : QuasithinUnique.Vol2Native.A312ListFactsCat)
    (h1227 : Stmt12_2_7) (h1228 : Stmt12_2_8) (h1229 : Stmt12_2_9) : Stmt12_3_1 :=
  stmt12_3_1_of_owed h1222 h331 h1225 h12212 h12213 hC27 VolI.asc129Statement_holds hC111 hC19
    (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) h3214 hC41 asB56_holds
    B5.asB51_holds hF314 hList h1227 h1228 h1229

end CFSG.Quasithin.H13.A7
