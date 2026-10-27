module

public import CFSG.Quasithin.H13.A5S1327a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def UH (_S : Setting G T L V) (H : Subgroup G) : Subgroup G :=
  conjClosure (quasithinOmegaOneCenter T) H

@[expose] noncomputable def HStar (S : Setting G T L V) (H : Subgroup G) :
    Subgroup (MulAut ↥(S.UH H)) :=
  autOn H (S.UH H)

@[expose] noncomputable def H0 (_S : Setting G T L V) (H : Subgroup G) : Subgroup G :=
  borelL T L ⊔ H

end Setting

@[expose] def ThreeTop {G : Type} [Group G] (X : Subgroup G) : Prop :=
  IsPGroup 3 ↥(oTwoUpper (⊤ : Subgroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X)))

@[expose] def Lemma13213 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
    Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)) → ¬ ThreeTop (S.H0 H)

@[expose] def CaseS2_1327 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
      Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))

@[expose] def O2H0One1327 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
    Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)) → pCoreOf 2 (S.H0 H) ≠ ⊥

@[expose] def Final1327 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
    Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)) → pCoreOf 2 (S.H0 H) ≠ ⊥ →
    ¬ ThreeTop (S.H0 H) → False

theorem rest1327_of (h13 : Lemma13213) (hS2 : CaseS2_1327) (hO2 : O2H0One1327)
    (hfin : Final1327) : Rest1327 := by
  intro G _ _ T L V S H hH hHZ hsolv
  have hS3 := hS2 G T L V S H hH hHZ hsolv
  exact hfin G T L V S H hH hHZ hsolv hS3 (hO2 G T L V S H hH hHZ hsolv hS3)
    (h13 G T L V S H hH hHZ hsolv hS3)

theorem stmt13_2_7_of_parts_ofNoN
    (h331 : Stmt3_3_1) (h523 : Stmt5_2_3) (h1222 : Stmt12_2_2) (hE22 : E2.E22StatementNoN)
    (hRes : Res1328a) (h13 : Lemma13213) (hS2 : CaseS2_1327) (hO2 : O2H0One1327)
    (hfin : Final1327) : Stmt13_2_7 :=
  stmt13_2_7_ofNoN h331 h523 h1222 hE22 hRes (rest1327_of h13 hS2 hO2 hfin)

end CFSG.Quasithin.H13.A5
