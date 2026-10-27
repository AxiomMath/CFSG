module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

namespace OrthPlacement

open CFSG.StandardType.GGQ2Frame.OrthBlocks

@[expose] def OrthInnerDiagData : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2},
    GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel (.orthogonal δ) t) 3 E H →
    4 ≤ t + δ.val →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
        Nat.card K = 2 ∧ commutator H = ⊤ ∧
        ∃ (θ : ↥H ⧸ Subgroup.center ↥H ≃* ↥(omegaQ (K := K) t δ))
          (hEN : E ≤ Subgroup.normalizer (H : Set G)),
          ∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈ LargeEvenInnSet ↥(omegaQ (K := K) t δ)

@[expose] def ExistsOrthFrame : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] (θ : ↥H ⧸ Subgroup.center ↥H ≃* ↥(omegaQ (K := K) t δ)),
    Nat.card K = 2 → commutator H = ⊤ → IsElemAbelian 3 E → 4 ≤ t + δ.val →
    ∀ (hEN : E ≤ Subgroup.normalizer (H : Set G)),
    (∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈ LargeEvenInnSet ↥(omegaQ (K := K) t δ)) →
    (∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E) →
    E ⊓ Subgroup.centralizer (H : Set G) = ⊥ → ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) →
    3 ^ 3 ≤ Nat.card E →
    ∃ ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K,
      Function.Injective ζ ∧ Nat.card E = 3 ^ t ∧ Nonempty (OrthFrame H E hEN K t δ ζ)

@[expose] def OrthEleH : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (_ : OrthFrame H E hEN K t δ ζ),
    Nat.card K = 2 → commutator H = ⊤ → IsElemAbelian 3 E →
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) → E ≤ H

@[expose] def OrthSmallRankVacuous : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2},
    GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel (.orthogonal δ) t) 3 E H →
    t + δ.val ≤ 3 → IsElemAbelian 3 E →
    (∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E) →
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) → Nat.card E < 3 ^ 4

@[expose] def OrthComponentOccursIff : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : OrthCtx H E hEN K t δ ζ)
    (A : Subgroup G), A ≤ E → ∀ X : Subgroup G,
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ c : PlaneRaw.Code t, (planeEntry (.orthogonal δ) t).admissible c ∧
        (planeEntry (.orthogonal δ) t).occurs (ggLinImage (p := 3) ctx.fr.coord A) c ∧
        X = ctx.fr.component c

@[expose] def OrthComponentCentEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : OrthCtx H E hEN K t δ ζ)
    (c : PlaneRaw.Code t), (planeEntry (.orthogonal δ) t).admissible c →
    ggLinImage (p := 3) ctx.fr.coord (Subgroup.centralizer (ctx.fr.component c : Set G)) =
      (planeEntry (.orthogonal δ) t).cent c

@[expose] def OrthComponentInsideEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : OrthCtx H E hEN K t δ ζ)
    (c : PlaneRaw.Code t), (planeEntry (.orthogonal δ) t).admissible c →
    ggLinImage (p := 3) ctx.fr.coord (ctx.fr.component c) = (planeEntry (.orthogonal δ) t).inside c

@[expose] def OrthComponentMarked : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : OrthCtx H E hEN K t δ ζ)
    (c : PlaneRaw.Code t), (planeEntry (.orthogonal δ) t).admissible c →
    LargeEvenMarking ↥(ctx.fr.component c)
      (fun lab _ _ _ _ _ => lab = (planeEntry (.orthogonal δ) t).label c)

end OrthPlacement

namespace OrthBlocks

@[expose] def OrthTauMemOmega : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → ∀ u : PlaneRaw.V t, otau ζ t δ u ∈ omegaQ (K := K) t δ

@[expose] def OrthIsComponentOfGlBlockCentralizer : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2] (t : ℕ) (δ : Fin 2)
    (S : Set (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)), (∀ s ∈ S, ∀ s' ∈ S, Commute s s') →
    ∀ {J' : Subgroup ↥(omegaQ (K := K) t δ)},
      IsComponentOf J' ((Subgroup.centralizer S).comap (omegaQ (K := K) t δ).subtype) →
      ∃ ε, IsPrimAdjIdemIn (RingHom.id K)
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val)) (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
          (Algebra.adjoin K (Units.val '' S)) ε ∧
        IsComponentOf J' ⁅glBlockCentralizer (omegaQ (K := K) t δ).subtype S ε,
          glBlockCentralizer (omegaQ (K := K) t δ).subtype S ε⁆

@[expose] def OrthIsQuasisimpleYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), PlaneRaw.admissible (.orthogonal δ) c → IsQuasisimple ↥(oYcode ζ t δ c)

@[expose] def OrthNotIsComponentOfYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), ¬ PlaneRaw.admissible (.orthogonal δ) c →
      ∀ X : Subgroup ↥(omegaQ (K := K) t δ), ¬ IsComponentOf X (oYcode ζ t δ c)

@[expose] def OrthIsComponentOfCentralizerTorusSetIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) (X : Subgroup ↥(omegaQ (K := K) t δ)),
      IsComponentOf X
          ((Subgroup.centralizer (oTorusSet ζ t δ U)).comap (omegaQ (K := K) t δ).subtype) ↔
        ∃ c : PlaneRaw.Code t, PlaneRaw.admissible (.orthogonal δ) c ∧ PlaneRaw.occurs U c ∧
          X = oYcode ζ t δ c

@[expose] def OrthTauMemYcodeIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), PlaneRaw.admissible (.orthogonal δ) c → ∀ u : PlaneRaw.V t,
      otau ζ t δ u ∈ (oYcode ζ t δ c).map (omegaQ (K := K) t δ).subtype ↔
        u ∈ PlaneRaw.inside (.orthogonal δ) c

@[expose] def OrthTauCommuteYcodeIff : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), PlaneRaw.admissible (.orthogonal δ) c → ∀ u : PlaneRaw.V t,
      (∀ g ∈ oYcode ζ t δ c, otau ζ t δ u * (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
          (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u) ↔
        u ∈ PlaneRaw.cent (.orthogonal δ) c

@[expose] def OrthMarkedYcode : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ (c : PlaneRaw.Code t), PlaneRaw.admissible (.orthogonal δ) c →
      LargeEvenMarking ↥(oYcode ζ t δ c)
        (fun lab _ _ _ _ _ => lab = PlaneRaw.label (.orthogonal δ) c)

end OrthBlocks

end

end CFSG.StandardType.GGQ2Frame
