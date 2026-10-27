module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

namespace LinPlacement

open CFSG.StandardType.GGQ2Frame.LinBlocks

@[expose] def LinInnerDiagData : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {r : ℕ},
    GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, 1⟩) 3 E H →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
        Nat.card K = 2 ∧ commutator H = ⊤ ∧
        ∃ (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K))
          (hEN : E ≤ Subgroup.normalizer (H : Set G)),
          ∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈
            LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) Set.univ

@[expose] def LinA1FourVacuous : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G},
    GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, 1, 2⟩) 3 E H → IsElemAbelian 3 E →
      ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) → ¬ 3 ^ 4 ≤ Nat.card E

@[expose] def ExistsLinFrame : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {r t : ℕ} {ε : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2]
    (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)),
    2 * t + ε.val = r + 1 → Nat.card K = 2 → commutator H = ⊤ → IsElemAbelian 3 E →
    ∀ (hEN : E ≤ Subgroup.normalizer (H : Set G)),
    (∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) Set.univ) →
    (∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E) →
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) → 3 ^ 3 ≤ Nat.card E →
    ∃ ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K,
      Function.Injective ζ ∧ Nat.card E = 3 ^ t ∧ Nonempty (LinFrame H E hEN K t ε ζ)

@[expose] def LinEleH : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {ε : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (_ : LinFrame H E hEN K t ε ζ),
    commutator H = ⊤ → IsElemAbelian 3 E → ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) →
    E ≤ H

@[expose] def LinComponentOccursIff : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {ε : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : LinCtx H E hEN K t ε ζ)
    (A : Subgroup G), A ≤ E → ∀ X : Subgroup G,
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ c : PlaneRaw.Code t, PlaneRaw.admissible (.linear ε) c ∧
        (planeEntry (.linear ε) t).occurs (ggLinImage (p := 3) ctx.fr.coord A) c ∧
        X = ctx.fr.component c

@[expose] def LinComponentCentEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {ε : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : LinCtx H E hEN K t ε ζ)
    (c : PlaneRaw.Code t), PlaneRaw.admissible (.linear ε) c →
    ggLinImage (p := 3) ctx.fr.coord (Subgroup.centralizer (ctx.fr.component c : Set G)) =
      (planeEntry (.linear ε) t).cent c

@[expose] def LinComponentInsideEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {ε : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : LinCtx H E hEN K t ε ζ)
    (c : PlaneRaw.Code t), PlaneRaw.admissible (.linear ε) c →
    ggLinImage (p := 3) ctx.fr.coord (ctx.fr.component c) = (planeEntry (.linear ε) t).inside c

@[expose] def LinComponentMarked : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {ε : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : LinCtx H E hEN K t ε ζ)
    (c : PlaneRaw.Code t), PlaneRaw.admissible (.linear ε) c →
    LargeEvenMarking ↥(ctx.fr.component c)
      (fun lab _ _ _ _ _ => lab = (planeEntry (.linear ε) t).label c)

end LinPlacement

namespace LinBlocks

@[expose] def LinIsPrimIdemInKeyIdem : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code t), PlaneRaw.occurs U c →
      0 < keyDim ε c →
      IsPrimIdemIn (Algebra.adjoin K (Units.val '' torusSet ζ t ε U)) (keyIdem t ε c)

@[expose] def LinExistsCodeOfIsPrimIdemIn : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) {P : Matrix (LinIdx t ε) (LinIdx t ε) K},
      IsPrimIdemIn (Algebra.adjoin K (Units.val '' torusSet ζ t ε U)) P →
      ∃ c : PlaneRaw.Code t, PlaneRaw.occurs U c ∧ 0 < keyDim ε c ∧ P = keyIdem t ε c

@[expose] def LinGlBlockCentralizerKeyIdem : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code t), PlaneRaw.occurs U c →
      0 < keyDim ε c →
      glBlockCentralizer (MonoidHom.id (GL (LinIdx t ε) K)) (torusSet ζ t ε U) (keyIdem t ε c) =
        blockGroup ζ t ε c

@[expose] def LinNormalYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code t), PlaneRaw.occurs U c →
      0 < keyDim ε c →
      ((Ycode ζ t ε c).subgroupOf (Subgroup.centralizer (torusSet ζ t ε U))).Normal

@[expose] def LinYcodeLeCentralizer : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code t), PlaneRaw.occurs U c →
      0 < keyDim ε c →
      Ycode ζ t ε c ≤ Subgroup.centralizer (torusSet ζ t ε U)

@[expose] def LinIsQuasisimpleYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), PlaneRaw.admissible (.linear ε) c → IsQuasisimple ↥(Ycode ζ t ε c)

@[expose] def LinNotIsComponentOfYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), ¬ PlaneRaw.admissible (.linear ε) c →
      ∀ X : Subgroup (GL (LinIdx t ε) K), ¬ IsComponentOf X (Ycode ζ t ε c)

@[expose] def LinIsComponentOfCentralizerTorusSetIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) (X : Subgroup (GL (LinIdx t ε) K)),
      IsComponentOf X (Subgroup.centralizer (torusSet ζ t ε U)) ↔
        ∃ c : PlaneRaw.Code t, PlaneRaw.admissible (.linear ε) c ∧ PlaneRaw.occurs U c ∧
          X = Ycode ζ t ε c

@[expose] def LinTauMemYcodeIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), PlaneRaw.admissible (.linear ε) c → ∀ u : PlaneRaw.V t,
      tau ζ t ε u ∈ Ycode ζ t ε c ↔ u ∈ PlaneRaw.inside (.linear ε) c

@[expose] def LinTauCommuteYcodeIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), PlaneRaw.admissible (.linear ε) c → ∀ u : PlaneRaw.V t,
      (∀ g ∈ Ycode ζ t ε c, tau ζ t ε u * g = g * tau ζ t ε u) ↔
        u ∈ PlaneRaw.cent (.linear ε) c

@[expose] def LinMarkedYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), PlaneRaw.admissible (.linear ε) c →
      LargeEvenMarking ↥(Ycode ζ t ε c)
        (fun lab _ _ _ _ _ => lab = PlaneRaw.label (.linear ε) c)

end LinBlocks

end

end CFSG.StandardType.GGQ2Frame
