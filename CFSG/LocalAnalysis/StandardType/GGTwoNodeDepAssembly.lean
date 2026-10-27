module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProof
public import CFSG.LocalAnalysis.StandardType.GGE6DepPerpDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARank
public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGRowKSide
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepTwoK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggRowTwoNodeSmall (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNode p J X ∧ X.rank ≤ 9

theorem GGResRowAt.twoNode_split {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    (h : GGResRowAt ggRowTwoNode p J X) :
    GGResRowAt ggRowTwoNodeSmall p J X ∨ GGResRowAt ggRowTwoNodeLarge p J X := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := h
  rcases le_or_gt labX.rank 9 with hle | hgt
  · exact Or.inl ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr, hle⟩⟩
  · exact Or.inr ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr, by omega⟩⟩

@[expose] def GGResTwoNodeDepSmallInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ x L _ J y K =>
    (GGResRowAt ggRowTwoNodeSmall p J L ∧ x ∉ L) ∨ (GGResRowAt ggRowTwoNodeSmall p J K ∧ y ∉ K)

theorem l05nAS_nonLevi_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTwo : GGResRowAt ggRowTwoNode p J K → GGResTwoNodeSideDatum p Bs K J)
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput)
    (h6e : GGResTriD4TwE6Input) (h6f : GGResSevenInput) (h6g : GGResTwA2Input)
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (h : GGResRowAt ggRowNonLevi p J K) :
    GGResTwoNodeSideDatum p Bs K J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases h.cases with h2 | h2 | h2 | h2 | h2 | h2
  · exact Or.inl (hTwo h2)
  · exact Or.inr (h6c G p B Bs x L D J y K hH hF hS hE (Or.inr h2))
  · exact Or.inr (h6d G p B Bs x L D J y K hH hF hS hE (Or.inr h2))
  · exact Or.inr (h6e G p B Bs x L D J y K hH hF hS hE (Or.inr h2))
  · exact Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inr h2))
  · exact Or.inr (h6g G p B Bs x L D J y K hH hF hS hE (Or.inr h2))

theorem l05nAS_nonLevi_L {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTwo : GGResRowAt ggRowTwoNode p J L → GGResTwoNodeSideDatum p Bs L J)
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput)
    (h6e : GGResTriD4TwE6Input) (h6f : GGResSevenInput) (h6g : GGResTwA2Input)
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (h : GGResRowAt ggRowNonLevi p J L) :
    GGResTwoNodeSideDatum p Bs L J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases h.cases with h2 | h2 | h2 | h2 | h2 | h2
  · exact Or.inl (hTwo h2)
  · exact Or.inr (h6c G p B Bs x L D J y K hH hF hS hE (Or.inl h2))
  · exact Or.inr (h6d G p B Bs x L D J y K hH hF hS hE (Or.inl h2))
  · exact Or.inr (h6e G p B Bs x L D J y K hH hF hS hE (Or.inl h2))
  · exact Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inl h2))
  · exact Or.inr (h6g G p B Bs x L D J y K hH hF hS hE (Or.inl h2))

private theorem l05nAS_shape_K (hJ : GGTBJInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hTwo : GGResXDatum p Bs K → GGResRowAt ggRowTwoNode p J K →
      GGResTwoNodeSideDatum p Bs K J) :
    GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases (hX G p B Bs x L D J y K hH).2 with hXK | hSK
  · rcases (hJ G p B Bs x L D J y K hH).2 hXK with hK | hNK
    · exact Or.inl hK
    · rcases l05nAS_nonLevi_K (hTwo hXK) h6c h6d h6e h6f h6g hH hF hS hE hNK with htwo | hweyl
      · exact Or.inr (Or.inl htwo)
      · exact Or.inr (Or.inr hweyl)
  · exact Or.inr (Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inr hSK)))

private theorem l05nAS_shape_L (hJ : GGTBJInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hTwo : GGResXDatum p Bs L → GGResRowAt ggRowTwoNode p J L →
      GGResTwoNodeSideDatum p Bs L J) :
    GGResSideDatum p Bs L J ∨ GGResTwoNodeSideDatum p Bs L J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases (hX G p B Bs x L D J y K hH).1 with hXL | hSL
  · rcases (hJ G p B Bs x L D J y K hH).1 hXL with hL | hNL
    · exact Or.inl hL
    · rcases l05nAS_nonLevi_L (hTwo hXL) h6c h6d h6e h6f h6g hH hF hS hE hNL with htwo | hweyl
      · exact Or.inr (Or.inl htwo)
      · exact Or.inr (Or.inr hweyl)
  · exact Or.inr (Or.inr (h6f G p B Bs x L D J y K hH hF hS hE (Or.inl hSL)))

theorem ggTwoNode_shape_K (hJ : GGTBJInput) (hJ2 : GGTBJTwoNodeInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K) :
    GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  exact l05nAS_shape_K hJ hX h6c h6d h6e h6f h6g hH hF hS hE
    (fun hXK h2 => (hJ2 G p B Bs x L D J y K hH).2 hXK h2)

theorem ggTwoNode_shape_L (hJ : GGTBJInput) (hJ2 : GGTBJTwoNodeInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K) :
    GGResSideDatum p Bs L J ∨ GGResTwoNodeSideDatum p Bs L J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  exact l05nAS_shape_L hJ hX h6c h6d h6e h6f h6g hH hF hS hE
    (fun hXL h2 => (hJ2 G p B Bs x L D J y K hH).1 hXL h2)

private lemma l05nAL_ggTorM_A {n rank : ℕ} :
    ggTorM (⟨.A, rank, n⟩ : LargeEvenLabel) = 2 ^ n - 1 := by
  have htag : (⟨.A, rank, n⟩ : LargeEvenLabel).tag = .A := rfl
  unfold ggTorM
  rw [htag]
  rw [if_neg (by decide : ¬ ((.A : LargeEvenLieTag) = .twA ∨
    (.A : LargeEvenLieTag) = .twE6))]

private lemma l05nAL_ggTorM_twA {n rank : ℕ} :
    ggTorM (⟨.twA, rank, n⟩ : LargeEvenLabel) = 2 ^ n + 1 := by
  have htag : (⟨.twA, rank, n⟩ : LargeEvenLabel).tag = .twA := rfl
  unfold ggTorM
  rw [htag]
  rw [if_pos (by decide : ((.twA : LargeEvenLieTag) = .twA ∨
    (.twA : LargeEvenLieTag) = .twE6))]

private lemma l05nAL_row_facts {p : ℕ} {J X : LargeEvenLabel}
    (h : ggRowTwoNode p J X) (h10 : 10 ≤ X.rank) :
    (X.tag = .A ∨ X.tag = .twA) ∧ 6 ≤ X.rank ∧ p ∣ X.rank + 1 ∧ p ∣ ggTorM X := by
  rcases h with ⟨-, hp1, hp2, hX⟩ | ⟨-, hp1, hp2, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    refine ⟨Or.inl rfl, by omega, ?_, ?_⟩
    · have he : (J.rank + 2) + 1 = J.rank + 3 := by omega
      rw [he]; exact hp2
    · rw [l05nAL_ggTorM_A]; exact hp1
  · subst hX
    refine ⟨Or.inr rfl, by omega, ?_, ?_⟩
    · have he : (J.rank + 2) + 1 = J.rank + 3 := by omega
      rw [he]; exact hp2
    · rw [l05nAL_ggTorM_twA]; exact hp1
  · subst hX
    have h0 : (⟨.E6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h10; omega
  · subst hX
    have h0 : (⟨.twE6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h10; omega

private lemma l05nAL_labelIso_eq {lab labX : LargeEvenLabel} (h : GGLabelIso lab labX)
    (htag : labX.tag = .A ∨ labX.tag = .twA) (h10 : 10 ≤ labX.rank) : lab = labX := by
  rcases h with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · rcases htag with hA | hA
    · rcases h2 with hB | hC
      · rw [hA] at hB; exact absurd hB (by decide)
      · rw [hA] at hC; exact absurd hC (by decide)
    · rcases h2 with hB | hC
      · rw [hA] at hB; exact absurd hB (by decide)
      · rw [hA] at hC; exact absurd hC (by decide)
  · rw [h2] at h10
    have h0 : (⟨.A, 3, lab.n⟩ : LargeEvenLabel).rank = 3 := rfl
    rw [h0] at h10; omega
  · rw [h2] at htag
    have h0 : (⟨.D, 3, lab.n⟩ : LargeEvenLabel).tag = .D := rfl
    rw [h0] at htag
    rcases htag with hA | hA <;> exact absurd hA (by decide)
  · rw [h2] at h10
    have h0 : (⟨.twA, 3, lab.n⟩ : LargeEvenLabel).rank = 3 := rfl
    rw [h0] at h10; omega
  · rw [h2] at htag
    have h0 : (⟨.twD, 3, lab.n⟩ : LargeEvenLabel).tag = .twD := rfl
    rw [h0] at htag
    rcases htag with hA | hA <;> exact absurd hA (by decide)
  · rw [h2] at h10
    have h0 : (⟨.A, 1, 2 * lab.n⟩ : LargeEvenLabel).rank = 1 := rfl
    rw [h0] at h10; omega
  · rw [h1] at htag
    have h0 : (⟨.twD, 2, labX.n⟩ : LargeEvenLabel).tag = .twD := rfl
    rw [h0] at htag
    rcases htag with hA | hA <;> exact absurd hA (by decide)

theorem ggTwoNodeLarge_false_L_narrow (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hT : GGTBTorANarrow)
    (hLift : GGTBTorLiftADepRows)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeLarge p J L) (hxL : x ∉ L)
    (hK : GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGResLeviSideDatumLE3 p Bs K J) : False := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRow⟩ := hrow
  obtain ⟨hRowNode, h10⟩ := hRow
  obtain ⟨htagX, h6X, hdvdX, hMX⟩ := l05nAL_row_facts hRowNode h10
  have hInner : GGInnerDiagOn Bs L := hH.2.2.1.1
  obtain ⟨hperf, lab0, hlab0, hraw0⟩ := hInner
  have hhas0 : GGHasLabel lab0 (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw0
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hlab0X : lab0 = labX :=
    l05nAL_labelIso_eq (hRig lab0 labX _ hlab0 hXΛ hhas0 hXlab) htagX h10
  have hInnerLabel : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧
      6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs L := by
    refine ⟨hperf, lab0, hlab0, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw0
    rintro R _ I F ⟨hs, hna, θ, hP0⟩
    exact ⟨hs, hna, θ, ⟨by rw [hlab0X]; exact ⟨htagX, h6X, hdvdX, hMX⟩, hP0⟩⟩
  obtain ⟨lab, hlab, hhas, htag', h6', hdvd', hM', hdat⟩ :=
    ggResXDatumA_of_tbTorA_rank hT hLift hH hInnerLabel
  have hlabX : lab = labX :=
    l05nAL_labelIso_eq (hRig lab labX _ hlab hXΛ hhas hXlab) htagX h10
  subst lab
  obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hCL, hφ, hrefl, hpair,
    ⟨f, hf⟩, hAL⟩ := hdat
  letI : Fintype Λ := iF
  letI : DecidableEq Λ := iD
  letI : AddCommGroup V := iAC
  letI : Module (ZMod p) V := iM
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hN : 11 ≤ labX.rank + 1 := by omega
  exact ggTwoNodeAtL_false hKG hOrb hFix hFixK hp2 hH hx hxL hN hdvd' e hMeq hCL hφ hpair hAL hK

theorem ggTwoNodeLarge_false_L (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeLarge p J L) (hxL : x ∉ L)
    (hK : GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGResLeviSideDatumLE3 p Bs K J) : False := by
  exact ggTwoNodeLarge_false_L_narrow hKG hOrb hFix hFixK (ggTBTorANarrow_of_all hT)
    (ggTBTorLiftADepRows_of_rows hLift) hRig hH hrow hxL hK

theorem l05nAK_iso_eq {labX labK : LargeEvenLabel} (hiso : GGLabelIso labX labK)
    (htag : labX.tag = .A ∨ labX.tag = .twA) (hrank : 4 ≤ labX.rank) :
    labX = labK := by
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h
  · rcases htag with ht | ht
    · rw [ht] at h; simp at h
    · rw [ht] at h; simp at h
  · rw [h.1] at hrank; simp at hrank
  · rw [h.1] at hrank; simp at hrank
  · rw [h.1] at hrank; simp at hrank
  · rw [h.1] at hrank; simp at hrank
  · rw [h.1] at hrank; simp at hrank
  · rw [h.2] at hrank; simp at hrank

theorem l05nAK_row_facts {p : ℕ} {labJ labX : LargeEvenLabel}
    (h : ggRowTwoNode p labJ labX) (hr : 10 ≤ labX.rank) :
    (labX.tag = .A ∨ labX.tag = .twA) ∧ p ∣ labX.rank + 1 ∧ p ∣ ggTorM labX := by
  rcases h with ⟨-, hq, hdvd, hX⟩ | ⟨-, hq, hdvd, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    exact ⟨Or.inl rfl, by simpa using hdvd, by simpa [ggTorM] using hq⟩
  · subst hX
    exact ⟨Or.inr rfl, by simpa using hdvd, by simpa [ggTorM] using hq⟩
  · subst hX
    simp at hr
  · subst hX
    simp at hr

theorem l05nAK_innerDiagOnLabel (hRig : GGLabelRigidInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {labX : LargeEvenLabel}
    (hXΛ : LargeEvenInLambda2 labX) (hXlab : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K))
    (htag : labX.tag = .A ∨ labX.tag = .twA) (hrank : 10 ≤ labX.rank)
    (hdvd : p ∣ labX.rank + 1) (hdvdM : p ∣ ggTorM labX) :
    GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs K := by
  obtain ⟨hcomm, labK, hlabK, hraw⟩ :=
    (hH.2.2.1.2 y K hH.2.2.2.2.1 : GGInnerDiagOn Bs K)
  have hlabKHas : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    exact ⟨θ⟩
  have hiso : GGLabelIso labX labK :=
    hRig labX labK (↥K ⧸ Subgroup.center ↥K) hXΛ hlabK hXlab hlabKHas
  have hEq : labX = labK := l05nAK_iso_eq hiso htag (by omega)
  refine ⟨hcomm, labK, hlabK, ?_⟩
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, hP⟩
  refine ⟨hs, hna, θ, ?_, hP⟩
  rw [← hEq]
  exact ⟨htag, by omega, hdvd, hdvdM⟩

theorem ggTwoNodeLarge_false_K_narrow (hKG : GGReflClassLargeInput')
    (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hT : GGTBTorANarrow)
    (hLift : GGTBTorLiftADepRows)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeLarge p J K) (hyK : y ∉ K)
    (hKd : GGResTwoNodeSideDatum p Bs K J)
    (hL : GGResSideDatum p Bs L J ∨ GGResTwoNodeSideDatum p Bs L J ∨
      GGResLeviSideDatumLE3 p Bs L J) : False := by
  have hrow0 := hrow
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRow⟩ := hrow
  obtain ⟨hRow2, hrankX⟩ := hRow
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨htagX, hdvdX, hdvdMX⟩ := l05nAK_row_facts hRow2 hrankX
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hIlab := l05nAK_innerDiagOnLabel hRig hH hXΛ hXlab htagX hrankX hdvdX hdvdMX
  obtain ⟨lab, hlabΛ, hlabHas, hlabTag, hlabRank, hlabDvd, hlabDvdM, hDatumLab⟩ :=
    ggResXDatumA_of_tbTorA_rank_K hT hLift hH hIlab
  have hiso2 : GGLabelIso lab labX :=
    hRig lab labX (↥K ⧸ Subgroup.center ↥K) hlabΛ hXΛ hlabHas hXlab
  have hEq2 : lab = labX := l05nAK_iso_eq hiso2 hlabTag (by omega)
  have hDatumX : GGResXDatumA p Bs K labX.rank := hEq2 ▸ hDatumLab
  obtain ⟨Λ, iF, iD, M, C, V, iVadd, iVmod, ι, φ, h, α, e, hM, hMw, hMC, hφ, hrefl,
    hpair, hIsoK, hAK⟩ := hDatumX
  letI : AddCommGroup V := iVadd
  letI : Module (ZMod p) V := iVmod
  obtain ⟨Λ', iF', iD', b₁, b₂, M', C', MJ, V', iV', iM', ι', φ', h', α',
    hb, hMw', hMC', hMJw, hMJeq, hφ', hrefl', hpair', hIsoK', hAK', hIsoJ', hAJ',
    hconj⟩ := hKd
  have hJK : ggAutomizer J Bs ≤ ggAutomizer K Bs := by
    rw [hAJ', hAK']
    apply Subgroup.closure_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨j, rfl⟩
  have hN : 11 ≤ labX.rank + 1 := by omega
  have hpN : p ∣ labX.rank + 1 := hdvdX
  exact ggTwoNodeAtK_false hKG hOrbK hFix hFixK hp2 hH hrow0 hy hyK hN hpN e hM hMC hφ hpair hAK
    hJK hL

theorem ggTwoNodeLarge_false_K (hKG : GGReflClassLargeInput') (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeLarge p J K) (hyK : y ∉ K)
    (hKd : GGResTwoNodeSideDatum p Bs K J)
    (hL : GGResSideDatum p Bs L J ∨ GGResTwoNodeSideDatum p Bs L J ∨
      GGResLeviSideDatumLE3 p Bs L J) : False := by
  exact ggTwoNodeLarge_false_K_narrow hKG hOrbK hFix hFixK (ggTBTorANarrow_of_all hT)
    (ggTBTorLiftADepRows_of_rows hLift) hRig hH hrow hyK hKd hL

lemma l05nAS_J_of_large {p : ℕ} {J X : LargeEvenLabel} (h : ggRowTwoNode p J X)
    (h10 : 10 ≤ X.rank) : (J.tag = .A ∨ J.tag = .twA) ∧ 8 ≤ J.rank := by
  rcases h with ⟨ht, -, -, hX⟩ | ⟨ht, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    have h' : 10 ≤ J.rank + 2 := h10
    exact ⟨Or.inl ht, by omega⟩
  · subst hX
    have h' : 10 ≤ J.rank + 2 := h10
    exact ⟨Or.inr ht, by omega⟩
  · subst hX
    have h' : 10 ≤ 0 := h10
    omega
  · subst hX
    have h' : 10 ≤ 0 := h10
    omega

theorem l05nAS_row_large (hRig : GGLabelRigidInput) {G : Type} [Group G] {p : ℕ}
    {J X : Subgroup G} (hJlab : ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ (labJ.tag = .A ∨ labJ.tag = .twA) ∧
      8 ≤ labJ.rank)
    (h2 : GGResRowAt ggRowTwoNode p J X) : GGResRowAt ggRowTwoNodeLarge p J X := by
  obtain ⟨labJ, hΛ, hhas, htag, h8⟩ := hJlab
  obtain ⟨labJ', labX', hJΛ', hXΛ', hJl', hXl', hr⟩ := h2
  have hEq : labJ = labJ' :=
    l05nAK_iso_eq (hRig labJ labJ' (↥J ⧸ Subgroup.center ↥J) hΛ hJΛ' hhas hJl') htag (by omega)
  subst hEq
  have hrk : 10 ≤ labX'.rank := by
    rcases hr with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨hD, -, -, -⟩ | ⟨hD, -, -, -⟩
    · subst hX
      show 10 ≤ labJ.rank + 2
      omega
    · subst hX
      show 10 ≤ labJ.rank + 2
      omega
    · have h4 : labJ.rank = 4 := by rw [hD]
      omega
    · have h4 : labJ.rank = 4 := by rw [hD]
      omega
  exact ⟨labJ, labX', hΛ, hXΛ', hhas, hXl', hr, hrk⟩

theorem ggTwoNode_shape_K_narrow (hJ : GGTBJInput) (hJ2 : GGTBJTwoNodeLargeInput)
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
    GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  exact l05nAS_shape_K hJ hX h6c h6d h6e h6f h6g hH hF hS hE
    (fun hXK h2 => (hJ2 G p B Bs x L D J y K hH).2 hXK (l05nAS_row_large hRig hJlab h2))

theorem ggTwoNode_shape_L_narrow (hJ : GGTBJInput) (hJ2 : GGTBJTwoNodeLargeInput)
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
    GGResSideDatum p Bs L J ∨ GGResTwoNodeSideDatum p Bs L J ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  exact l05nAS_shape_L hJ hX h6c h6d h6e h6f h6g hH hF hS hE
    (fun hXL h2 => (hJ2 G p B Bs x L D J y K hH).1 hXL (l05nAS_row_large hRig hJlab h2))

theorem ggResTwoNodeDepInput_of_small_narrow (hSmall : GGResTwoNodeDepSmallInput)
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput) (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hT : GGTBTorANarrow)
    (hLift : GGTBTorLiftADepRows) (hRig : GGLabelRigidInput) (hJ : GGTBJInput)
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
    · rcases ggTwoNode_shape_K_narrow hJ hJ2 hRig hX h6c h6d h6e h6f h6g hH hF hS hE
          (hJlab hlg) with hK1 | hK2 | hW
      · exfalso
        exact ggTwoNodeLarge_false_L_narrow hKG hOrb hFix hFixK hT hLift hRig hH hlg hxL
          (Or.inl hK1)
      · exfalso
        exact ggTwoNodeLarge_false_L_narrow hKG hOrb hFix hFixK hT hLift hRig hH hlg hxL
          (Or.inr (Or.inl hK2))
      · exact hW
  · rcases hrowK.twoNode_split with hsm | hlg
    · exact hSmall G p B Bs x L D J y K hH hF hS hE (Or.inr ⟨hsm, hyK⟩)
    · rcases (hX G p B Bs x L D J y K hH).2 with hXK | hSK
      · have hKd : GGResTwoNodeSideDatum p Bs K J :=
          (hJ2 G p B Bs x L D J y K hH).2 hXK hlg
        rcases ggTwoNode_shape_L_narrow hJ hJ2 hRig hX h6c h6d h6e h6f h6g hH hF hS hE
          (hJlab hlg) with hL1 | hL2 | hW
        · exfalso
          exact ggTwoNodeLarge_false_K_narrow hKG hOrbK hFix hFixK hT hLift hRig hH hlg hyK hKd
            (Or.inl hL1)
        · exfalso
          exact ggTwoNodeLarge_false_K_narrow hKG hOrbK hFix hFixK hT hLift hRig hH hlg hyK hKd
            (Or.inr (Or.inl hL2))
        · exact hW
      · exact h6f G p B Bs x L D J y K hH hF hS hE (Or.inr hSK)

theorem ggResTwoNodeDepInput_of_small (hSmall : GGResTwoNodeDepSmallInput)
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput) (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hRig : GGLabelRigidInput) (hJ : GGTBJInput) (hJ2 : GGTBJTwoNodeInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) : GGResTwoNodeDepInput := by
  exact ggResTwoNodeDepInput_of_small_narrow hSmall hKG hOrb hOrbK hFix hFixK
    (ggTBTorANarrow_of_all hT) (ggTBTorLiftADepRows_of_rows hLift) hRig hJ
    (ggTBJTwoNodeLargeInput_of_input hJ2) hX h6c h6d h6e h6f h6g

end CFSG.StandardType
