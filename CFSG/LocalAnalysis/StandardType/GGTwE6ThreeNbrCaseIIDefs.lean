module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

@[expose] def GGTwE6ThreeNbrCaseII : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K → ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGTorusSelfCent 3 (ggGamma K hN).range →
        B = Bs → Nat.card Bs = 3 ^ 5 → LargeEvenTwoLocalRank 3 G = 5 →
        Nat.card (ggGamma K hN).range = 3 ^ 4 →
        Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y → False

end CFSG.StandardType

end
