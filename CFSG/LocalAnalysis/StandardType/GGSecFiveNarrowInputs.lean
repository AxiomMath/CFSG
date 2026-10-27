module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGRealQFour

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSecFivePumpLInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      GGWeylReflectionGroup p (ggAutomizer L Bs) ∧
        ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer L Bs)

@[expose] def GGSecFivePumpNbrInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
          ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs)

@[expose] def GGSecFivePumpReadInput
    : Prop :=
  GGSecFivePumpLInput ∧ GGSecFivePumpNbrInput

@[expose] def GGReflRealizedQFourNbrInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' 3 B Bs x L D J 𝒦 → GGSplitLie 3 L →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
        GGInnerDiagOnLabel GGLabQFour 3 Bs K → GGReflRealizedIn 3 Bs K

end CFSG.StandardType

end
