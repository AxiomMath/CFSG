module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeLE3Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNode_shape_K_narrowR (hJ : GGTBJInputR) (hJ2 : GGTBJTwoNodeLargeInput)
    (hRig : GGLabelRigidInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hJlab : ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ (labJ.tag = .A ∨ labJ.tag = .twA) ∧
      8 ≤ labJ.rank) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases (hX G p B Bs x L D J y K hH).2 with hXK | hSK
  · rcases (hJ G p B Bs x L D J y K hH).2 hXK with hK | hK3 | hNK
    · exact Or.inl hK
    · exact Or.inr (Or.inl hK3)
    · rcases l05nAS_nonLevi_K
          (fun h2 => (hJ2 G p B Bs x L D J y K hH).2 hXK (l05nAS_row_large hRig hJlab h2))
          h6c h6d h6e h6f h6g hH hF hS hE hNK with htwo | hweyl
      · exact Or.inr (Or.inr (Or.inl htwo))
      · exact Or.inr (Or.inr (Or.inr hweyl))
  · exact Or.inr (Or.inr (Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inr hSK))))

theorem ggTwoNode_shape_L_narrowR (hJ : GGTBJInputR) (hJ2 : GGTBJTwoNodeLargeInput)
    (hRig : GGLabelRigidInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hJlab : ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ (labJ.tag = .A ∨ labJ.tag = .twA) ∧
      8 ≤ labJ.rank) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J ∨ GGResTwoNodeSideDatum p Bs L J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases (hX G p B Bs x L D J y K hH).1 with hXL | hSL
  · rcases (hJ G p B Bs x L D J y K hH).1 hXL with hL | hL3 | hNL
    · exact Or.inl hL
    · exact Or.inr (Or.inl hL3)
    · rcases l05nAS_nonLevi_L
          (fun h2 => (hJ2 G p B Bs x L D J y K hH).1 hXL (l05nAS_row_large hRig hJlab h2))
          h6c h6d h6e h6f h6g hH hF hS hE hNL with htwo | hweyl
      · exact Or.inr (Or.inr (Or.inl htwo))
      · exact Or.inr (Or.inr (Or.inr hweyl))
  · exact Or.inr (Or.inr (Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inl hSL))))

theorem ggResTwoNodeDepInput_of_small_narrowR (hSmall : GGResTwoNodeDepSmallInput)
    (hLE3 : GGResTwoNodeLE3Input)
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput) (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hT : GGTBTorANarrow)
    (hLift : GGTBTorLiftADepRows) (hRig : GGLabelRigidInput) (hJ : GGTBJInputR)
    (hJ2 : GGTBJTwoNodeLargeInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) : GGResTwoNodeDepInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  have hJlab : ∀ {J X : Subgroup G}, GGResRowAt ggRowTwoNodeLarge p J X →
      ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ (labJ.tag = .A ∨ labJ.tag = .twA) ∧
        8 ≤ labJ.rank := by
    intro J X hlg
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := hlg
    obtain ⟨ht, h8⟩ := l05nAS_J_of_large hr.1 hr.2
    exact ⟨labJ, hJΛ, hJl, ht, h8⟩
  rcases hP with ⟨hrowL, hxL⟩ | ⟨hrowK, hyK⟩
  · rcases hrowL.twoNode_split with hsm | hlg
    · exact hSmall G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨hsm, hxL⟩)
    · rcases ggTwoNode_shape_K_narrowR hJ hJ2 hRig hX h6c h6d h6e h6f h6g hH hF hS hE
          (hJlab hlg) with hK1 | hK3 | hK2 | hW
      · exfalso
        exact ggTwoNodeLarge_false_L_narrow hKG hOrb hFix hFixK hT hLift hRig hH hlg hxL
          (Or.inl hK1)
      · exact hLE3 G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨hlg, hxL, hK3⟩)
      · exfalso
        exact ggTwoNodeLarge_false_L_narrow hKG hOrb hFix hFixK hT hLift hRig hH hlg hxL
          (Or.inr (Or.inl hK2))
      · exact hW
  · rcases hrowK.twoNode_split with hsm | hlg
    · exact hSmall G p B Bs x L D J y K hH hF hS hE (Or.inr ⟨hsm, hyK⟩)
    · rcases (hX G p B Bs x L D J y K hH).2 with hXK | hSK
      · have hKd : GGResTwoNodeSideDatum p Bs K J :=
          (hJ2 G p B Bs x L D J y K hH).2 hXK hlg
        rcases ggTwoNode_shape_L_narrowR hJ hJ2 hRig hX h6c h6d h6e h6f h6g hH hF hS hE
          (hJlab hlg) with hL1 | hL3 | hL2 | hW
        · exfalso
          exact ggTwoNodeLarge_false_K_narrow hKG hOrbK hFix hFixK hT hLift hRig hH hlg hyK hKd
            (Or.inl hL1)
        · exact hLE3 G p B Bs x L D J y K hH hF hS hE (Or.inr ⟨hlg, hyK, hL3⟩)
        · exfalso
          exact ggTwoNodeLarge_false_K_narrow hKG hOrbK hFix hFixK hT hLift hRig hH hlg hyK hKd
            (Or.inr (Or.inl hL2))
        · exact hW
      · exact h6f G p B Bs x L D J y K hH hF hS hE (Or.inr hSK)

theorem ggResTwoNodeLE3Input_proved (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows) (hRig : GGLabelRigidInput)
    (hJ2 : GGTBJTwoNodeLargeInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6f : GGResSevenInput) : GGResTwoNodeLE3Input := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases hP with ⟨hlg, hxL, hK3⟩ | ⟨hlg, hyK, hL3⟩
  · exact (ggTwoNodeLarge_false_L_narrow hKG hOrb hFix hFixK hT hLift hRig hH hlg hxL
      (Or.inr (Or.inr hK3))).elim
  · rcases (hX G p B Bs x L D J y K hH).2 with hXK | hSK
    · exact (ggTwoNodeLarge_false_K_narrow hKG hOrbK hFix hFixK hT hLift hRig hH hlg hyK
        ((hJ2 G p B Bs x L D J y K hH).2 hXK hlg) (Or.inr (Or.inr hL3))).elim
    · exact h6f G p B Bs x L D J y K hH hF hS hE (Or.inr hSK)

end CFSG.StandardType

end
