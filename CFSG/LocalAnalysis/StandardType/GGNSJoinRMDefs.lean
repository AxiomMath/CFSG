module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinContracts
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxOfInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin


@[expose] def NSRegularCfgOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) {G : Type} [Group G]
    [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop :=
  GGSecFiveRouteCfg p B Bs x L D J 𝒦 ∧ ¬ GGSplitLie p L ∧ NSJoinGuardOf T p L Bs 𝒦

@[expose] def NSRegularCfg {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)) : Prop :=
  NSRegularCfgOf NSTypeAD p B Bs x L D J 𝒦

@[expose] def NSFixInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x

@[expose] def NSJA2InputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs, GGIsReflection p r ∧ GGIsReflection p r' ∧
        orderOf (r * r') = 3

@[expose] def NSJA2Input : Prop :=
  NSJA2InputOf NSTypeAD

@[expose] def NSPumpLInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      GGWeylReflectionGroup p (ggAutomizer L Bs) ∧ ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer L Bs)

@[expose] def NSPumpNbrInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
          ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs)

@[expose] def NSPumpNbrInput : Prop :=
  NSPumpNbrInputOf NSTypeAD

@[expose] def NSRootGenLInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      ∀ r ∈ ggAutomizer L Bs, GGIsReflection p r → GGRealized p Bs r

@[expose] def NSRealNbrInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T 3 B Bs x L D J 𝒦 →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
        GGInnerDiagOnLabel GGLabQFour 3 Bs K → GGReflRealizedIn 3 Bs K

@[expose] def NSNbrQFourInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T 3 B Bs x L D J 𝒦 →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K → GGInnerDiagOnLabel GGLabQFour 3 Bs K

@[expose] def NSNbrQFourInput : Prop :=
  NSNbrQFourInputOf NSTypeAD

@[expose] def NSQFourInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      GGInnerDiagOnLabel GGLabQFour p Bs L

end NSJoin

end CFSG.StandardType

end
