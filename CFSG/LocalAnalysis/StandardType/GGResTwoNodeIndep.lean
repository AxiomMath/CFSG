module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssemblyR

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTwoNodeIndepInput_of_parts (hL : GGResTwoNodeIndepLargeInput)
    (hS : GGResTwoNodeIndepSmallInput) : GGResTwoNodeIndepInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS' hE hP
  rcases hP with ⟨hrowL, hxL⟩ | ⟨hrowK, hyK⟩
  · rcases hrowL.twoNode_splitLK with h | h
    · exact hL G p B Bs x L D J y K hH hF hS' hE (Or.inl ⟨h, hxL⟩)
    · exact hS G p B Bs x L D J y K hH hF hS' hE (Or.inl ⟨h, hxL⟩)
  · rcases hrowK.twoNode_splitLK with h | h
    · exact hL G p B Bs x L D J y K hH hF hS' hE (Or.inr ⟨h, hyK⟩)
    · exact hS G p B Bs x L D J y K hH hF hS' hE (Or.inr ⟨h, hyK⟩)

@[expose] def GGResTwoNodeIndepLE3RestInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs x L _ J y K =>
    (GGResRowAt ggRowTwoNodeSmallA p J L ∧ x ∈ L ∧ GGResLeviSideDatumLE3 p Bs K J) ∨
    (GGResRowAt ggRowTwoNodeSmallA p J K ∧ y ∈ K ∧ GGResLeviSideDatumLE3 p Bs L J) ∨
    (GGResRowAt ggRowTwoNodeNine p J L ∧ x ∈ L ∧ x ∉ (ggBstarComm L Bs).map Bs.subtype ∧
      GGResLeviSideDatumLE3 p Bs K J) ∨
    (GGResRowAt ggRowTwoNodeNine p J K ∧ y ∈ K ∧ y ∉ (ggBstarComm K Bs).map Bs.subtype ∧
      GGResLeviSideDatumLE3 p Bs L J)

@[expose] def GGResTwoNodeIndepLE3E6Input : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs x L _ J y K =>
    (GGResRowAt ggRowTwoNodeSmallA p J L ∧ p = 3 ∧ x ∈ L ∧ Nat.card ↥Bs = 3 ^ 6 ∧
        GGResLeviSideDatumLE3 p Bs K J ∧ ¬ GGResTwoNodeSideDatum p Bs K J) ∨
      (GGResRowAt ggRowTwoNodeSmallA p J K ∧ p = 3 ∧ y ∈ K ∧ Nat.card ↥Bs = 3 ^ 6 ∧
        GGResLeviSideDatumLE3 p Bs L J ∧ ¬ GGResTwoNodeSideDatum p Bs L J) ∨
      (GGResRowAt ggRowTwoNodeNine p J K ∧ y ∈ K ∧ y ∉ (ggBstarComm K Bs).map Bs.subtype ∧
        Nat.card ↥Bs = 3 ^ 10 ∧ GGResLeviSideDatumLE3 p Bs L J ∧
        ¬ GGResTwoNodeSideDatum p Bs L J)

@[expose] def GGResTwoNodeIndepLE3TenInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J y K =>
    GGResRowAt ggRowTwoNodeNine p J K ∧ y ∈ K ∧ y ∉ (ggBstarComm K Bs).map Bs.subtype ∧
      Nat.card ↥Bs = 3 ^ 10 ∧ GGResLeviSideDatumLE3 p Bs L J ∧
      ¬ GGResTwoNodeSideDatum p Bs L J

theorem ggTwoNode_shape_K_R (hJ : GGTBJInputR) (hJ2 : GGTBJTwoNodeInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases (hX G p B Bs x L D J y K hH).2 with hXK | hSK
  · rcases (hJ G p B Bs x L D J y K hH).2 hXK with hK | hK3 | hNK
    · exact Or.inl hK
    · exact Or.inr (Or.inl hK3)
    · rcases l05nAS_nonLevi_K (fun h2 => (hJ2 G p B Bs x L D J y K hH).2 hXK h2)
          h6c h6d h6e h6f h6g hH hF hS hE hNK with htwo | hweyl
      · exact Or.inr (Or.inr (Or.inl htwo))
      · exact Or.inr (Or.inr (Or.inr hweyl))
  · exact Or.inr (Or.inr (Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inr hSK))))

theorem ggTwoNode_shape_L_R (hJ : GGTBJInputR) (hJ2 : GGTBJTwoNodeInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J ∨ GGResTwoNodeSideDatum p Bs L J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases (hX G p B Bs x L D J y K hH).1 with hXL | hSL
  · rcases (hJ G p B Bs x L D J y K hH).1 hXL with hL | hL3 | hNL
    · exact Or.inl hL
    · exact Or.inr (Or.inl hL3)
    · rcases l05nAS_nonLevi_L (fun h2 => (hJ2 G p B Bs x L D J y K hH).1 hXL h2)
          h6c h6d h6e h6f h6g hH hF hS hE hNL with htwo | hweyl
      · exact Or.inr (Or.inr (Or.inl htwo))
      · exact Or.inr (Or.inr (Or.inr hweyl))
  · exact Or.inr (Or.inr (Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inl hSL))))

theorem ggResTwoNodeIndepSmallRest_of_two (h2 : GGResTwoNodeIndepSmallTwoInput)
    (hLE3 : GGResTwoNodeIndepLE3RestInput) (hJ : GGTBJInputR) (hJ2 : GGTBJTwoNodeInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) : GGResTwoNodeIndepSmallRestInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases hP with ⟨hrow, hxL⟩ | ⟨hrow, hyK⟩ | ⟨hrow, hxL, hnK⟩ | ⟨hrow, hyK, hnL⟩
  · exact h2 G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨hrow, hxL⟩)
  · exact h2 G p B Bs x L D J y K hH hF hS hE (Or.inr (Or.inl ⟨hrow, hyK⟩))
  · rcases ggTwoNode_shape_K_R hJ hJ2 hX h6c h6d h6e h6f h6g hH hF hS hE with hK1 | hK3 | hK2 | hW
    · exact absurd hK1 hnK
    · exact hLE3 G p B Bs x L D J y K hH hF hS hE
        (Or.inl ⟨hrow, hxL, hK3⟩)
    · exact h2 G p B Bs x L D J y K hH hF hS hE (Or.inr (Or.inr (Or.inl ⟨hrow, hxL, hK2⟩)))
    · exact hW
  · rcases ggTwoNode_shape_L_R hJ hJ2 hX h6c h6d h6e h6f h6g hH hF hS hE with hL1 | hL3 | hL2 | hW
    · exact absurd hL1 hnL
    · exact hLE3 G p B Bs x L D J y K hH hF hS hE
        (Or.inr (Or.inl ⟨hrow, hyK, hL3⟩))
    · exact h2 G p B Bs x L D J y K hH hF hS hE (Or.inr (Or.inr (Or.inr ⟨hrow, hyK, hL2⟩)))
    · exact hW

end CFSG.StandardType

end
