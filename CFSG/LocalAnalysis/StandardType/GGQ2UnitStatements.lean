module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def UnitInnerDiagData : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ},
    GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, N - 1, 1⟩) 3 E H →
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧ 4 ≤ N ∧ commutator H = ⊤ ∧
        ∃ (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (unitarySU 2 1 K N))
          (hEN : E ≤ Subgroup.normalizer (H : Set G)),
          ∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈
            LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K N))
              (LargeEvenGUSet (Fin N) K (2 ^ 1))

@[expose] def ExistsUnitFrame : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K] [Finite K]
    (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (unitarySU 2 1 K N)),
    Nat.card K = 4 → 4 ≤ N → commutator H = ⊤ → IsElemAbelian 3 E →
    ∀ (hEN : E ≤ Subgroup.normalizer (H : Set G)),
    (∀ (b : G) (hb : b ∈ E), ggLAut H θ ⟨b, hEN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K N))
        (LargeEvenGUSet (Fin N) K (2 ^ 1))) →
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) → 3 ^ 4 ≤ Nat.card E →
    (3 ∣ N → 3 ^ (N - 3) ≤ Nat.card E) →
    ∃ ζ : Multiplicative (ZMod 3) →* Kˣ, Function.Injective ζ ∧ 5 ≤ N ∧
      Nonempty (UnitFrame H E hEN K N ζ)

@[expose] def UnitFrameRange : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K] [Finite K]
    {hEN : E ≤ Subgroup.normalizer (H : Set G)} {ζ : Multiplicative (ZMod 3) →* Kˣ}
    (fr : UnitFrame H E hEN K N ζ), Nat.card K = 4 → Function.Injective ζ → 5 ≤ N →
    (∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E) →
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) →
    fr.ι.range = ⊤ ∨ (3 ∣ N ∧ fr.ι.range = (UnitRaw.heart N).toAddSubgroup)

@[expose] def UnitComponentOccursIff : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K] [Finite K]
    {hEN : E ≤ Subgroup.normalizer (H : Set G)} {ζ : Multiplicative (ZMod 3) →* Kˣ}
    (ctx : UnitCtx H E hEN K N ζ) (A : Subgroup G), A ≤ E → ∀ X : Subgroup G,
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ S : Finset (Fin N), UnitRaw.admissible S ∧ UnitRaw.occurs (ctx.fr.image A) S ∧
        X = ctx.fr.component S

@[expose] def UnitComponentCentEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K] [Finite K]
    {hEN : E ≤ Subgroup.normalizer (H : Set G)} {ζ : Multiplicative (ZMod 3) →* Kˣ}
    (ctx : UnitCtx H E hEN K N ζ) (S : Finset (Fin N)), UnitRaw.admissible S →
    ctx.fr.image (Subgroup.centralizer (ctx.fr.component S : Set G)) =
      UnitRaw.cent S ⊓ ctx.fr.image E

@[expose] def UnitComponentInsideEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K] [Finite K]
    {hEN : E ≤ Subgroup.normalizer (H : Set G)} {ζ : Multiplicative (ZMod 3) →* Kˣ}
    (ctx : UnitCtx H E hEN K N ζ) (S : Finset (Fin N)), UnitRaw.admissible S →
    ctx.fr.image (ctx.fr.component S) = UnitRaw.inside S ⊓ ctx.fr.image E

@[expose] def UnitComponentMarked : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K] [Finite K]
    {hEN : E ≤ Subgroup.normalizer (H : Set G)} {ζ : Multiplicative (ZMod 3) →* Kˣ}
    (ctx : UnitCtx H E hEN K N ζ) (S : Finset (Fin N)), UnitRaw.admissible S →
    LargeEvenMarking ↥(ctx.fr.component S) (fun lab _ _ _ _ _ => lab = UnitRaw.label S)

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement
