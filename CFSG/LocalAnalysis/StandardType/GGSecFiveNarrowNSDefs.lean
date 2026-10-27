module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGSecFivePumpNbrNSInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ¬ GGSplitLie p K →
        GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
          ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs)

@[expose] def GGReflRealizedQFourNbrNSInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' 3 B Bs x L D J 𝒦 → GGSplitLie 3 L →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K → ¬ GGSplitLie 3 K →
        GGInnerDiagOnLabel GGLabQFour 3 Bs K → GGReflRealizedIn 3 Bs K

end CFSG.StandardType

end
