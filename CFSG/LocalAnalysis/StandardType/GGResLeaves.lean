module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGResRows

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResLeviDatum p Bs L J K ggSelAny ggTypAny ∨
      GGResRowAt ggRowNonLevi p J L ∨ GGResRowAt ggRowNonLevi p J K

@[expose] def GGResCaseIQFourInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    GGResLeviDatum p Bs L J K ggSelI (ggTypRankLt 8) ∧ ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L

@[expose] def GGResCaseIQTwoInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    GGResLeviDatum p Bs L J K ggSelI (ggTypRankLt 8) ∧ GGInnerDiagOnLabel GGLabQTwo p Bs L

@[expose] def GGResCaseIISmallInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K => GGResLeviDatum p Bs L J K ggSelII (ggTypRankLt 9)

@[expose] def GGResDepTypeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResLeviDatum p Bs L J K ggSelDep ggTypAny →
      (p = 3 ∧ GGResLeviDatum p Bs L J K ggSelDep ggTypLE6) ∨
        GGResLeviDatum p Bs L J K ggSelDep ggTypLA

@[expose] def GGResE6DepShape {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs L J K : Subgroup G) :
    Prop :=
  p = 3 ∧ Nat.card Bs = 3 ^ 6 ∧ GGResLeviDatum p Bs L J K ggSelDep ggTypLKE6

@[expose] def GGResDepE6Input : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    p = 3 ∧ GGResLeviDatum p Bs L J K ggSelDep ggTypLE6 ∧ ¬ GGResE6DepShape p Bs L J K

@[expose] def GGResE6DepLabelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResE6DepShape p Bs L J K →
      ∃ lab₀ : LargeEvenLabel, GGE6DepLabel lab₀ ∧
        LargeEvenMarking L (fun lab _ _ _ _ _ => lab = lab₀) ∧
        LargeEvenMarking K (fun lab _ _ _ _ _ => lab = lab₀)

@[expose] def GGResDepAThreeInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    p = 3 ∧ GGResLeviDatum p Bs L J K ggSelDep ggTypLA

@[expose] def GGResDepAFiveInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    p ≠ 3 ∧ GGResLeviDatum p Bs L J K ggSelDep ggTypLA

@[expose] def GGResTwoNodeIndepInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ x L _ J y K =>
    (GGResRowAt ggRowTwoNode p J L ∧ x ∈ L) ∨ (GGResRowAt ggRowTwoNode p J K ∧ y ∈ K)

@[expose] def GGResTwoNodeDepInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ x L _ J y K =>
    (GGResRowAt ggRowTwoNode p J L ∧ x ∉ L) ∨ (GGResRowAt ggRowTwoNode p J K ∧ y ∉ K)

@[expose] def GGResMaxRankInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ _ L _ J _ K =>
    GGResRowAt ggRowMaxRank p J L ∨ GGResRowAt ggRowMaxRank p J K

@[expose] def GGResTrialityInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ _ L _ J _ K =>
    GGResRowAt ggRowTriality p J L ∨ GGResRowAt ggRowTriality p J K

@[expose] def GGResTriD4TwE6Input : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ _ L _ J _ K =>
    GGResRowAt ggRowTriD4TwE6 p J L ∨ GGResRowAt ggRowTriD4TwE6 p J K

@[expose] def GGResSevenInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ _ L _ J _ K =>
    GGResRowAt ggRowSeven p J L ∨ GGResRowAt ggRowSeven p J K

@[expose] def GGResTwA2Input : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ _ L _ J _ K =>
    GGResRowAt ggRowTwA2 p J L ∨ GGResRowAt ggRowTwA2 p J K

end CFSG.StandardType
