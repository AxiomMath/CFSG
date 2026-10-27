module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
  (t : ℕ) (δ : Fin 2)

@[expose] def oTorusAut (X : Subgroup ↥(omegaQ (K := K) t δ)) :
    Set (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) :=
  {φ | ∃ y ∈ X, ∀ u, (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u *
      (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)⁻¹ = otau ζ t δ (φ u)}

@[expose] def OrthAmbientTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ → 4 ≤ t →
      oTorusAut ζ t δ ⊤ = ((PlaneRaw.ambientNormalizer (.orthogonal δ) t : Subgroup _) : Set _)

@[expose] def OrthComponentTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ → 4 ≤ t →
    ∀ c : PlaneRaw.Code t, PlaneRaw.admissible (.orthogonal δ) c →
      oTorusAut ζ t δ (oYcode ζ t δ c) =
        ((PlaneRaw.normalizerOf (.orthogonal δ) t c : Subgroup _) : Set _)

@[expose] def OrthZeroTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ → 4 ≤ t →
    ∀ S : Finset (Fin t), PlaneRaw.admissible (.orthogonal δ) (.zero S) →
      oTorusAut ζ t δ (oYcode ζ t δ (.zero S)) =
        ((PlaneRaw.normalizerOf (.orthogonal δ) t (.zero S) : Subgroup _) : Set _)

@[expose] def OrthExtTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
    Nat.card K = 2 → Function.Injective ζ → 4 ≤ t →
    ∀ e : PlaneRaw.V t, 4 ≤ (PlaneRaw.Code.extSupport e).card →
      oTorusAut ζ t δ (oYcode ζ t δ (.extension e)) =
        ((PlaneRaw.normalizerOf (.orthogonal δ) t (.extension e) : Subgroup _) : Set _)

theorem orthComponentTorusAut_of_parts (hz : OrthZeroTorusAut) (he : OrthExtTorusAut) :
    OrthComponentTorusAut := by
  intro K _ _ _ ζ t δ hK hζ ht c hc
  cases c with
  | zero S => exact hz ζ t δ hK hζ ht S hc
  | extension e => exact he ζ t δ hK hζ ht e hc.2

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
