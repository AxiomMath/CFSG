module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2CoverDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2SpRealizationDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

namespace SpPlacement

open CFSG.StandardType.GGQ2Frame.SpBlocks

@[expose] def SpInnerDiagData : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ},
    GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel .symplectic m) 3 E H →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : NeZero m),
        Nat.card K = 2 ∧ commutator H = ⊤ ∧
        ∃ (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSpGroup K m))
          (hEN : E ≤ Subgroup.normalizer (H : Set G)),
          ∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈
            LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)

@[expose] def ExistsSpFrame : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] [NeZero m] (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSpGroup K m)),
    Nat.card K = 2 → commutator H = ⊤ → IsElemAbelian 3 E →
    ∀ (hEN : E ≤ Subgroup.normalizer (H : Set G)),
    (∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) →
    (∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E) →
    E ⊓ Subgroup.centralizer (H : Set G) = ⊥ → 3 ^ 3 ≤ Nat.card E →
    ∃ ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K,
      Function.Injective ζ ∧ Nat.card E = 3 ^ m ∧ Nonempty (SpFrame H E hEN K m ζ)

@[expose] def SpEleH : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (_ : SpFrame H E hEN K m ζ),
    commutator H = ⊤ → IsElemAbelian 3 E → ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) →
    E ≤ H

@[expose] def SpComponentOccursIff : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : SpCtx H E hEN K m ζ)
    (A : Subgroup G), A ≤ E → ∀ X : Subgroup G,
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ c : PlaneRaw.Code m, PlaneRaw.admissible .symplectic c ∧
        (planeEntry .symplectic m).occurs (ggLinImage (p := 3) ctx.fr.coord A) c ∧
        X = ctx.fr.component c

@[expose] def SpComponentCentEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : SpCtx H E hEN K m ζ)
    (c : PlaneRaw.Code m), PlaneRaw.admissible .symplectic c →
    ggLinImage (p := 3) ctx.fr.coord (Subgroup.centralizer (ctx.fr.component c : Set G)) =
      (planeEntry .symplectic m).cent c

@[expose] def SpComponentInsideEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : SpCtx H E hEN K m ζ)
    (c : PlaneRaw.Code m), PlaneRaw.admissible .symplectic c →
    ggLinImage (p := 3) ctx.fr.coord (ctx.fr.component c) = (planeEntry .symplectic m).inside c

@[expose] def SpComponentMarked : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : SpCtx H E hEN K m ζ)
    (c : PlaneRaw.Code m), PlaneRaw.admissible .symplectic c →
    LargeEvenMarking ↥(ctx.fr.component c)
      (fun lab _ _ _ _ _ => lab = (planeEntry .symplectic m).label c)

end SpPlacement

namespace SpBlocks

@[expose] def SpExistsCodeOfIsPrimAdjIdemIn : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V m)) {ε : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K},
      IsPrimAdjIdemIn (RingHom.id K)
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
        (Algebra.adjoin K (Units.val '' torusSet ζ m U)) ε →
      ∃ c : PlaneRaw.Code m, PlaneRaw.occurs U c ∧ c.support.Nonempty ∧ ε = planeIdem m c.support

@[expose] def SpGlBlockCentralizerPlaneIdem : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V m)) (c : PlaneRaw.Code m), PlaneRaw.occurs U c →
      c.support.Nonempty →
      glBlockCentralizer (StatedSp m K).subtype (torusSet ζ m U) (planeIdem m c.support) =
        blockGroup ζ m c

@[expose] def SpNormalYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V m)) (c : PlaneRaw.Code m), PlaneRaw.occurs U c →
      c.support.Nonempty →
      ((Ycode ζ m c).subgroupOf
        ((Subgroup.centralizer (torusSet ζ m U)).comap (StatedSp m K).subtype)).Normal

@[expose] def SpYcodeLeCentralizer : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V m)) (c : PlaneRaw.Code m), PlaneRaw.occurs U c →
      c.support.Nonempty →
      Ycode ζ m c ≤ (Subgroup.centralizer (torusSet ζ m U)).comap (StatedSp m K).subtype

@[expose] def SpIsQuasisimpleYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code m), PlaneRaw.admissible .symplectic c → IsQuasisimple ↥(Ycode ζ m c)

@[expose] def SpNotIsComponentOfYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code m), ¬ PlaneRaw.admissible .symplectic c →
      ∀ X : Subgroup ↥(StatedSp m K), ¬ IsComponentOf X (Ycode ζ m c)

@[expose] def SpIsComponentOfCentralizerTorusSetIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V m)) (X : Subgroup ↥(StatedSp m K)),
      IsComponentOf X ((Subgroup.centralizer (torusSet ζ m U)).comap (StatedSp m K).subtype) ↔
        ∃ c : PlaneRaw.Code m, PlaneRaw.admissible .symplectic c ∧ PlaneRaw.occurs U c ∧
          X = Ycode ζ m c

@[expose] def SpTauMemYcodeIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code m), PlaneRaw.admissible .symplectic c → ∀ u : PlaneRaw.V m,
      tau ζ m u ∈ Ycode ζ m c ↔ u ∈ PlaneRaw.inside .symplectic c

@[expose] def SpTauCommuteYcodeIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code m), PlaneRaw.admissible .symplectic c → ∀ u : PlaneRaw.V m,
      (∀ g ∈ Ycode ζ m c, tau ζ m u * g = g * tau ζ m u) ↔ u ∈ PlaneRaw.cent .symplectic c

@[expose] def SpMarkedYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code m), PlaneRaw.admissible .symplectic c →
      LargeEvenMarking ↥(Ycode ζ m c)
        (fun lab _ _ _ _ _ => lab = PlaneRaw.label .symplectic c)

end SpBlocks

namespace CoverComponents

@[expose] def IsComponentOfCoverIff : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* R),
    IsPGroup 3 A → Function.Surjective π → π.ker ≤ Subgroup.center ↥H → ¬ 3 ∣ Nat.card π.ker →
    commutator H = ⊤ → Equivariant hAN π ρ → ∀ X : Subgroup G,
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ Y : Subgroup R, IsComponentOf Y (Subgroup.centralizer ((ρ.range : Subgroup R) : Set R)) ∧
        X = (⁅Y.comap π, Y.comap π⁆).map H.subtype

@[expose] def CommuteCoverIff : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* R),
    π.ker ≤ Subgroup.center ↥H → Equivariant hAN π ρ →
    ∀ X : Subgroup ↥H, commutator X = ⊤ → ∀ e : ↥A,
    (∀ x ∈ X, (e : G) * (x : G) = (x : G) * (e : G)) ↔
      ∀ y ∈ X.map π, ρ e * y = y * ρ e

@[expose] def MemDerivedComapIff : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H : Subgroup G} {R : Type} [Group R] (π : ↥H →* R),
    Function.Surjective π → π.ker ≤ Subgroup.center ↥H → ¬ 3 ∣ Nat.card π.ker →
    ∀ Y : Subgroup R, ⁅Y, Y⁆ = Y → ∀ e : ↥H, e ^ 3 = 1 →
    (e ∈ ⁅Y.comap π, Y.comap π⁆ ↔ π e ∈ Y)

end CoverComponents

end

end CFSG.StandardType.GGQ2Frame
