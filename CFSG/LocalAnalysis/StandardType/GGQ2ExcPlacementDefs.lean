module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley Module
open CFSG.Open (IsElemAbelian)

noncomputable section

structure ModelFrame {M : Type} [Group M] (H E : Subgroup M) (R : RawFrameData) : Type where
  coord : Additive ↥E ≃+ R.V
  component : R.Code → Subgroup M
  component_le : ∀ c : R.Code, R.admissible c → component c ≤ H
  marked : ∀ c : R.Code, R.admissible c →
    LargeEvenMarking ↥(component c) (fun lab _ _ _ _ _ => lab = R.label c)
  occurs_iff : ∀ (A : Subgroup M), A ≤ E → ∀ X : Subgroup M,
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set M)) ↔
      ∃ c : R.Code, R.admissible c ∧ R.occurs (ggLinImage (p := 3) coord A) c ∧ X = component c
  cent_eq : ∀ c : R.Code, R.admissible c →
    ggLinImage (p := 3) coord (Subgroup.centralizer (component c : Set M)) = R.cent c
  inside_eq : ∀ c : R.Code, R.admissible c →
    ggLinImage (p := 3) coord (component c) = R.inside c
  normalizer_eq : ∀ c : R.Code, R.admissible c →
    (ggAutomizer (component c) E).map (ggLin (p := 3) coord) = R.normalizerGroup c
  ambientNormalizer_eq : (ggAutomizer H E).map (ggLin (p := 3) coord) = R.ambientNormalizer

@[expose] def Realization.ofModelFrame {G : Type} [Group G] {H E : Subgroup G} {R : RawFrameData}
    (mf : ModelFrame H E R)
    (hid : GGInnerDiagOnLabel (fun _ lab => lab = R.ambientLabel) 3 E H)
    (hroot : ∀ c : R.Code, R.admissible c → LinearMap.ker (R.rootMap c) ≤ R.cent c) :
    Realization H E R where
  coord := mf.coord
  component := mf.component
  innerDiag := hid
  component_le := mf.component_le
  marked := mf.marked
  occurs_iff := mf.occurs_iff
  cent_eq := mf.cent_eq
  inside_eq := mf.inside_eq
  root_le_cent := hroot
  normalizer_eq := mf.normalizer_eq
  ambientNormalizer_eq := mf.ambientNormalizer_eq

@[expose] def ModelFrame.CompNormal {M : Type} [Group M] {H E : Subgroup M} {R : RawFrameData}
    (mf : ModelFrame H E R) : Prop :=
  ∀ c : R.Code, R.admissible c → E ≤ Subgroup.normalizer (mf.component c : Set M)

@[expose] def CoverSelfCent : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type} [Group M] (_ : E ≤ H)
    (π : ↥H →* M), Function.Surjective π → π.ker ≤ Subgroup.center ↥H → ¬ 3 ∣ Nat.card π.ker →
    IsElemAbelian 3 E → (∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E) →
    IsElemAbelian 3 ((E.subgroupOf H).map π) ∧ Nat.card ((E.subgroupOf H).map π) = Nat.card E ∧
      ∀ g ∈ Subgroup.centralizer (((E.subgroupOf H).map π : Subgroup M) : Set M), g ^ 3 = 1 →
        g ∈ (E.subgroupOf H).map π

@[expose] def ModelFrameOfCover : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type} [Group M] {R : RawFrameData}
    (_ : E ≤ H) (π : ↥H →* M), Function.Surjective π → π.ker ≤ Subgroup.center ↥H →
    ¬ 3 ∣ Nat.card π.ker → commutator H = ⊤ → IsElemAbelian 3 E →
    ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R → Nonempty (ModelFrame H E R)

namespace ExcPlacement

@[expose] def ExcUntwCover (t : LargeEvenLieTag) (τ : Tag) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G},
    GGInnerDiagOnLabel (fun _ lab => lab = ⟨t, 0, 1⟩) 3 E H → IsElemAbelian 3 E →
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) →
    E ≤ H ∧ commutator H = ⊤ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      ∃ π : ↥H →* adjointGroup τ K, Function.Surjective π ∧ π.ker = Subgroup.center ↥H

@[expose] def ExcUntwTorusLift (τ : Tag) (r : ℕ) : Prop :=
  ∀ {K : Type} [Field K] [Finite K], Nat.card K = 2 → GGTorusLift 3 r ↥(adjointGroup τ K)

@[expose] def ExcUntwFrameOrder (τ : Tag) (r d : ℕ) : Prop :=
  ∀ {K : Type} [Field K] [Finite K], Nat.card K = 2 →
    ∀ {E : Subgroup (adjointGroup τ K)}, IsElemAbelian 3 E →
      (∀ g ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), g ^ 3 = 1 → g ∈ E) →
      3 ^ r ≤ Nat.card E → Nat.card E = 3 ^ d

@[expose] def ExcUntwModelFrame (m : Fin 6) (τ : Tag) : Prop :=
  ∀ {K : Type} [Field K] [Finite K], Nat.card K = 2 →
    ∀ {E : Subgroup (adjointGroup τ K)}, IsElemAbelian 3 E → Nat.card E = 3 ^ ExcRaw.dim m →
      (∀ g ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), g ^ 3 = 1 → g ∈ E) →
      Nonempty (ModelFrame (⊤ : Subgroup (adjointGroup τ K)) E (excRaw m))

@[expose] def ExcTwE6Placement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J →
    GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs (ggG0 3 B x L D J) →
      ActualFrame (ggG0 3 B x L D J) Bs (excRaw 2) ∨ ActualFrame (ggG0 3 B x L D J) Bs (excRaw 3)

end ExcPlacement

end

end CFSG.StandardType.GGQ2Frame
