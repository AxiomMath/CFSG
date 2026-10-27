module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosAmb
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

inductive FrameKind
  | lin (t : ℕ) (epsilon : Fin 2)
  | symp (t : ℕ)
  | orth (t : ℕ) (delta : Fin 2)
  | unitFull (N : ℕ)
  | unitHeart (N : ℕ)
  | exceptional (mode : Fin 6)
  deriving DecidableEq

@[expose] def IsClassical : FrameKind → Prop
  | .lin _ _ => True
  | .symp _ => True
  | .orth _ _ => True
  | .unitFull _ => True
  | .unitHeart _ => True
  | .exceptional _ => False

instance : DecidablePred IsClassical := fun k => by
  cases k <;> simp only [IsClassical] <;> infer_instance

@[expose] def IsExceptional (k : FrameKind) : Prop := ¬ IsClassical k

instance : DecidablePred IsExceptional := fun k =>
  inferInstanceAs (Decidable (¬ IsClassical k))

structure RawFrameData where
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod 3) V]
  [instFiniteDimensional : FiniteDimensional (ZMod 3) V]
  Code : Type
  [instFintype : Fintype Code]
  kind : FrameKind
  ambientLabel : LargeEvenLabel
  admissible : Code → Prop
  occurs : Submodule (ZMod 3) V → Code → Prop
  label : Code → LargeEvenLabel
  cent : Code → Submodule (ZMod 3) V
  inside : Code → Submodule (ZMod 3) V
  normalizerGroup : Code → Subgroup (V ≃ₗ[ZMod 3] V)
  ambientNormalizer : Subgroup (V ≃ₗ[ZMod 3] V)
  absRank : Code → ℕ
  rootMap : (c : Code) → V →ₗ[ZMod 3] (Fin (absRank c) → ZMod 3)
  equivLabels : Code → Set LargeEvenLabel
  Root : Type
  [instRootFintype : Fintype Root]
  root : Root → Module.Dual (ZMod 3) V
  coroot : Root → V
  pairing : Root → Root → ℤ
  pairing_eq : ∀ i j : Root, root i (coroot j) = (pairing i j : ZMod 3)
  pairing_self : ∀ i : Root, pairing i i = 2
  reflection : Root → (V ≃ₗ[ZMod 3] V)
  reflection_apply : ∀ (i : Root) (v : V), reflection i v = v - root i v • coroot i

attribute [instance] RawFrameData.instAddCommGroup RawFrameData.instModule
  RawFrameData.instFiniteDimensional RawFrameData.instFintype RawFrameData.instRootFintype

structure RealizationCore {G : Type} [Group G] (H E : Subgroup G) (R : RawFrameData) : Type where
  coord : Additive ↥E ≃+ R.V
  component : R.Code → Subgroup G
  innerDiag :
    GGInnerDiagOnLabel (fun _ lab => lab = R.ambientLabel) 3 E H
  component_le : ∀ c : R.Code, R.admissible c → component c ≤ H
  marked : ∀ c : R.Code, R.admissible c →
    LargeEvenMarking (component c) (fun lab _ _ _ _ _ => lab = R.label c)
  occurs_iff : ∀ (A : Subgroup G), A ≤ E → ∀ X : Subgroup G,
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ c : R.Code, R.admissible c ∧ R.occurs (ggLinImage (p := 3) coord A) c ∧
        X = component c
  cent_eq : ∀ c : R.Code, R.admissible c →
    ggLinImage (p := 3) coord (Subgroup.centralizer (component c : Set G)) = R.cent c
  inside_eq : ∀ c : R.Code, R.admissible c →
    ggLinImage (p := 3) coord (component c) = R.inside c
  root_le_cent : ∀ c : R.Code, R.admissible c →
    LinearMap.ker (R.rootMap c) ≤ R.cent c

structure RealizationCore.NormalizerEqs {G : Type} [Group G] {H E : Subgroup G}
    {R : RawFrameData} (core : RealizationCore H E R) : Prop where
  normalizer_eq : ∀ c : R.Code, R.admissible c →
    (ggAutomizer (core.component c) E).map (ggLin (p := 3) core.coord) = R.normalizerGroup c
  ambientNormalizer_eq :
    (ggAutomizer H E).map (ggLin (p := 3) core.coord) = R.ambientNormalizer

structure Realization {G : Type} [Group G] (H E : Subgroup G) (R : RawFrameData) : Type
    extends RealizationCore H E R where
  normalizer_eq : ∀ c : R.Code, R.admissible c →
    (ggAutomizer (component c) E).map (ggLin (p := 3) coord) = R.normalizerGroup c
  ambientNormalizer_eq :
    (ggAutomizer H E).map (ggLin (p := 3) coord) = R.ambientNormalizer

@[expose] def ActualFrame {G : Type} [Group G] (H E : Subgroup G) (R : RawFrameData) : Prop :=
  Nonempty (Realization H E R)

@[expose] def ActualCoreFrame {G : Type} [Group G] (H E : Subgroup G) (R : RawFrameData) : Prop :=
  Nonempty (RealizationCore H E R)

@[expose] def Realization.ofCore {G : Type} [Group G] {H E : Subgroup G} {R : RawFrameData}
    (core : RealizationCore H E R) (hn : core.NormalizerEqs) : Realization H E R :=
  { core with
    normalizer_eq := hn.normalizer_eq
    ambientNormalizer_eq := hn.ambientNormalizer_eq }

theorem ActualFrame.toCore {G : Type} [Group G] {H E : Subgroup G} {R : RawFrameData}
    (h : ActualFrame H E R) : ActualCoreFrame H E R :=
  h.elim fun real => ⟨real.toRealizationCore⟩

@[expose] def LiteralMark {G : Type} [Group G] (X : Subgroup G) (lab : LargeEvenLabel) : Prop :=
  LargeEvenMarking X (fun lab' _ _ _ _ _ => lab' = lab)

@[expose] def TwoNodeLabels (p : ℕ) (labX labJ : LargeEvenLabel) : Prop :=
  (labJ.tag = .A ∧ labX.tag = .A ∧ labX.rank = labJ.rank + 2 ∧ labX.n = labJ.n ∧
      p ∣ labJ.rank + 3 ∧ p ∣ 2 ^ labJ.n - 1) ∨
    (labJ.tag = .twA ∧ labX.tag = .twA ∧ labX.rank = labJ.rank + 2 ∧ labX.n = labJ.n ∧
      p ∣ labJ.rank + 3 ∧ p ∣ 2 ^ labJ.n + 1) ∨
    (labJ.tag = .D ∧ labJ.rank = 4 ∧ labX.tag = .E6 ∧ labX.n = labJ.n ∧ p = 3 ∧
      p ∣ 2 ^ labJ.n - 1) ∨
    (labJ.tag = .D ∧ labJ.rank = 4 ∧ labX.tag = .twE6 ∧ labX.n = labJ.n ∧ p = 3 ∧
      p ∣ 2 ^ labJ.n + 1)

theorem markedRow_iff {G : Type} [Group G] (p : ℕ) (X J : Subgroup G) :
    GGQTwoTwoNodeRowAt p X J ↔
      ∃ labX labJ : LargeEvenLabel,
        LiteralMark X labX ∧ LiteralMark J labJ ∧ TwoNodeLabels p labX labJ := by
  unfold GGQTwoTwoNodeRowAt LiteralMark TwoNodeLabels
  rfl

@[expose] def RawNoInternalTwoNode (R : RawFrameData) : Prop :=
  ∀ v : R.V, v ≠ 0 →
    ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → v ∈ U →
      ∀ k j : R.Code, R.admissible k → R.admissible j →
        R.occurs (Submodule.span (ZMod 3) {v}) k → R.occurs U j →
          R.cent k = Submodule.span (ZMod 3) {v} → R.cent j ≤ U → v ∈ R.inside k →
            ∀ labK ∈ R.equivLabels k, ∀ labJ ∈ R.equivLabels j,
              ¬ TwoNodeLabels 3 labK labJ

@[expose] def CutThreeInput (R : RawFrameData) : Prop :=
  IsClassical R.kind → RawNoInternalTwoNode R

@[expose] def CutFiveInput (R : RawFrameData) : Prop :=
  IsExceptional R.kind → RawNoInternalTwoNode R

@[expose] def LiteralDictionaryInput (R : RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] {H E : Subgroup G} (real : RealizationCore H E R),
    ∀ c : R.Code, R.admissible c →
      ∀ lab : LargeEvenLabel, LiteralMark (real.component c) lab → lab ∈ R.equivLabels c

@[expose] def PlacementInput (catalogue : FrameKind → RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 →
      ∃ kind : FrameKind,
        ActualFrame (ggG0 p B x L D J) Bs (catalogue kind)

@[expose] def PlacementCoreInput (catalogue : FrameKind → RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 →
      ∃ kind : FrameKind,
        ActualCoreFrame (ggG0 p B x L D J) Bs (catalogue kind)

@[expose] def AmbModelFromFrameInput (catalogue : FrameKind → RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime],
    (¬ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))) →
    (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ Nonempty (GGQTwoModel p Bs x y D L J K)) →
    ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ¬ GGQTwoTwoNodeRowAt p L J → ¬ GGQTwoTwoNodeRowAt p K J →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ kind : FrameKind,
        ActualFrame (ggG0 p B x L D J) Bs (catalogue kind) →
          ∃ M : GGQTwoAmbModel p Bs x y L (L ⊔ K), GGQTwoAmbBasis M ∧
            ((M.cartan.det : ℤ) : ZMod p) ≠ 0 ∧
            ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
              (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) ≠ 0

@[expose] def ActualInternalExclusion (R : RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E D J K : Subgroup G} {y : G},
    ActualCoreFrame H E R → D ≤ E → Nat.card D = 9 → y ∈ D → orderOf y = 3 →
      IsComponentOf K (H ⊓ Subgroup.centralizer ({y} : Set G)) →
      IsComponentOf J (H ⊓ Subgroup.centralizer (D : Set G)) → J ≤ K →
      E ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y →
      GGQTwoI1 E D J → GGQTwoTwoNodeRowAt 3 K J → y ∉ K

@[expose] def ActualCutThreeInput (R : RawFrameData) : Prop :=
  IsClassical R.kind → ActualInternalExclusion R

@[expose] def ActualCutFiveInput (R : RawFrameData) : Prop :=
  IsExceptional R.kind → ActualInternalExclusion R

end CFSG.StandardType.GGQ2Frame
