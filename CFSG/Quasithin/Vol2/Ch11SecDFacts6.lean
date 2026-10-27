module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts
public import CFSG.Quasithin.Background.G2L2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def TorusFixSL3Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (X : Subgroup G),
    NatSetting11 G T L I n → KindSL3 L (fsuV T I) n → IsCartanX T L X →
      fsuV T I ⊓ Subgroup.centralizer (X : Set G) = ⊥

@[expose] def CommLOneSL3Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    NatSetting11 G T L I n → KindSL3 L (fsuV T I) n → IsVi T L I n 1 V₁ →
      ⁅fsuV T I, LOf L V₁⁆ = fsuV T I

end CFSG.Quasithin.Vol2.Ch11.SecD
