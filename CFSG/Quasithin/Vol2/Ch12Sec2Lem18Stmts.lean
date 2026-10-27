module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem12218TwoRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Hyp1223 G T L V →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (L : Set G) →
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ∀ E : Subgroup G, E ≤ H → IsElemAbelian 2 E →
      E ⊓ Subgroup.centralizer (VZ T H : Set G) = ⊥ → Nat.card E ≤ 4

end CFSG.Quasithin.H13
