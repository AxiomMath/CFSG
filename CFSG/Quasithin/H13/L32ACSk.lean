module

public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, T ≤ Subgroup.normalizer (K : Set G)

@[expose] def Lemma14_7_33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ∀ n : ℕ, ¬ IsSz n (cStar K)

@[expose] def Lemma14_7_34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, CFSG.Open.pRank 3 K = 1 ∨ CFSG.Open.pRank 3 K = 2

@[expose] def Lemma14_7_49 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ¬ IsPSL 3 2 1 (cStar K) ∧ ¬ IsAlt 6 (cStar K)

@[expose] def Lemma14_7_50 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ¬ IsAlt 7 (cStar K)

@[expose] def Lemma14_7_51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ∀ n : ℕ, ¬ IsPSL n 2 1 (cStar K)

end CFSG.Quasithin.H13.L32A.C
