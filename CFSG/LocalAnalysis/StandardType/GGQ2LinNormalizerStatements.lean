module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def torusAut {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    (X : Subgroup (GL (LinIdx t ε) K)) : Set (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) :=
  {φ | ∃ y ∈ X, ∀ u, y * tau ζ t ε u * y⁻¹ = tau ζ t ε (φ u)}

@[expose] def LinAmbientTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
      torusAut ζ t ε ⊤ = ((PlaneRaw.ambientNormalizer (.linear ε) t : Subgroup _) : Set _)

@[expose] def LinComponentTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ c : PlaneRaw.Code t, PlaneRaw.admissible (.linear ε) c →
      torusAut ζ t ε (Ycode ζ t ε c) =
        ((PlaneRaw.normalizerOf (.linear ε) t c : Subgroup _) : Set _)

@[expose] def LinZeroTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ S : Finset (Fin t), 3 ≤ 2 * S.card + ε.val →
      torusAut ζ t ε (Ycode ζ t ε (.zero S)) =
        ((PlaneRaw.normalizerOf (.linear ε) t (.zero S) : Subgroup _) : Set _)

@[expose] def LinExtTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ e : PlaneRaw.V t, 2 ≤ (PlaneRaw.Code.extSupport e).card →
      torusAut ζ t ε (Ycode ζ t ε (.extension e)) =
        ((PlaneRaw.normalizerOf (.linear ε) t (.extension e) : Subgroup _) : Set _)

theorem linComponentTorusAut_of_parts (hz : LinZeroTorusAut) (he : LinExtTorusAut) :
    LinComponentTorusAut := by
  intro K _ _ _ ζ t ε hK hζ c hc
  cases c with
  | zero S => exact hz ζ t ε hK hζ S hc
  | extension e => exact he ζ t ε hK hζ e hc.2

end

end CFSG.StandardType.GGQ2Frame.LinBlocks
