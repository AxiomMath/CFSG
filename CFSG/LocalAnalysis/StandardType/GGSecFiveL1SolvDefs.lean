module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSecFiveAllFixedSolvInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)),
    GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
    ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
      Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G))

end CFSG.StandardType

end
