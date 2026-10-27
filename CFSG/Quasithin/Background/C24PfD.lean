module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Asc82Thm2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ X A K : Subgroup (MulAut W), CFSG.SectionRank.IsKGroupCat ↥X → IsFFStarOffender X A →
      K ≤ X → CFSG.IsComponent (K.subgroupOf X) →
        A ≤ Subgroup.normalizer (K : Set (MulAut W))

variable (G : Type) [Group G] [Finite G]

@[expose] def ASC24TwoChar : Prop :=
  ∀ H R M L : Subgroup G, HypC23 H R M → CharTwo H → L ∈ cComp H → CharTwo L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    (IsSylowTwoOf (R ⊓ L) L ∨ R ≤ Subgroup.normalizer (L : Set G))

end CFSG.Quasithin
