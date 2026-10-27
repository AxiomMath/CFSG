module

public import CFSG.Quasithin.H13.A5S1327u
public import CFSG.Quasithin.H13.A5S1327j

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def CaseS2A_1327 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
    ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)) → pCoreOf 2 (S.H0 H) = ⊥ → False

theorem caseS2_1327_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) (h1332 : Stmt13_3_2) (h512 : Stmt5_1_2)
    (h137 : EmptyFaithfulMultiple.Input137) (hA : CaseS2A_1327) : CaseS2_1327 := by
  intro G _ _ T L V S H hH hHZ hsolv
  by_contra hS3
  by_cases hO2 : pCoreOf 2 (S.H0 H) = ⊥
  · exact hA G T L V S H hH hHZ hsolv hS3 hO2
  · exact S.false_of_caseS2B h331 h1222 h5172 h1332 h512 h137 hH hHZ hsolv hS3 hO2

theorem stmt13_2_7_of_caseS2A_ofNoN
    (h331 : Stmt3_3_1) (h311 : Theorem311Stmt) (h432 : Stmt4_3_2) (h523 : Stmt5_2_3)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) (hE22 : E2.E22StatementNoN) (hRes : Res1328a)
    (hF618 : F6.TheoremF618Cat) (hBig : FactF618Big) (hL2 : FactL2Three) (h1332 : Stmt13_3_2)
    (h512 : Stmt5_1_2) (h137 : EmptyFaithfulMultiple.Input137) (hA : CaseS2A_1327) :
    Stmt13_2_7 :=
  stmt13_2_7_of_caseS2_ofNoN h331 h311 h432 h523 h1222 h5172 hE22 hRes hF618 hBig hL2
    (caseS2_1327_of h331 h1222 h5172 h1332 h512 h137 hA)

end CFSG.Quasithin.H13.A5
