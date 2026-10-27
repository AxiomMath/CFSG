module

public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_47_Hat6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (L32A.l1 T L V ⊔ T) →
      ¬ IsHat (L32A.cStar K) ↥(alternatingGroup (Fin 6))

@[expose] def Lemma14_7_47_L32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (L32A.l1 T L V ⊔ T) → IsPSL 3 2 1 (L32A.cStar K) →
      L32A.l1 T L V ≤ K

end CFSG.Quasithin.H13.L32A.C
