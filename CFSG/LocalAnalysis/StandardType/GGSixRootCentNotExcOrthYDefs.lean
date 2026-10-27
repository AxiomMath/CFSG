module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TInd
public import CFSG.LocalAnalysis.StandardType.GGStructSOneHolds

public section

namespace CFSG.StandardType

@[expose] def GGRootCentOrthYData {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G)
    (x : G) (L D J : Subgroup G) (r : G) : Prop :=
  ∃ y : G, y ∈ Subgroup.centralizer ({r} : Set G) ∧ orderOf y = 3 ∧
    Subgroup.centralizer ({y} : Set G) ≤ ggM p B x L D J ∧
    ∃ J₁ : Subgroup G, J₁ ≤ Subgroup.centralizer ({y} : Set G) ∧
      ∀ C : Subgroup (GGInvolCentBar (ggG0 p B x L D J) r), CFSG.Open.IsComponentOf C ⊤ →
        C ≤ (J₁.subgroupOf (Subgroup.centralizer ({r} : Set G) ⊓ ggG0 p B x L D J)).map
          (QuotientGroup.mk' (CFSG.Open.pCore 2
            ↥(Subgroup.centralizer ({r} : Set G) ⊓ ggG0 p B x L D J)))

end CFSG.StandardType
