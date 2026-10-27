module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

namespace SpBlocks

variable {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)

@[expose] def torusAut (X : Subgroup ↥(StatedSp m K)) :
    Set (PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m) :=
  {φ | ∃ y ∈ X, ∀ u, y * tau ζ m u * y⁻¹ = tau ζ m (φ u)}

@[expose] def SpAmbientTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
      torusAut ζ m ⊤ = ((PlaneRaw.ambientNormalizer .symplectic m : Subgroup _) : Set _)

@[expose] def SpComponentTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ c : PlaneRaw.Code m, PlaneRaw.admissible .symplectic c →
      torusAut ζ m (Ycode ζ m c) = ((PlaneRaw.normalizerOf .symplectic m c : Subgroup _) : Set _)

@[expose] def SpZeroTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ S : Finset (Fin m), 2 ≤ S.card →
      torusAut ζ m (Ycode ζ m (.zero S)) =
        ((PlaneRaw.normalizerOf .symplectic m (.zero S) : Subgroup _) : Set _)

@[expose] def SpExtTorusAut : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ),
    Nat.card K = 2 → Function.Injective ζ →
    ∀ e : PlaneRaw.V m, 4 ≤ (PlaneRaw.Code.extSupport e).card →
      torusAut ζ m (Ycode ζ m (.extension e)) =
        ((PlaneRaw.normalizerOf .symplectic m (.extension e) : Subgroup _) : Set _)

theorem spComponentTorusAut_of_parts (hz : SpZeroTorusAut) (he : SpExtTorusAut) :
    SpComponentTorusAut := by
  intro K _ _ _ ζ m hK hζ c hc
  cases c with
  | zero S => exact hz ζ m hK hζ S hc
  | extension e => exact he ζ m hK hζ e hc.2

end SpBlocks

namespace CoverComponents

@[expose] def AutomizerCoverEq : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H A : Subgroup G} {R : Type} [Group R]
    (hAH : A ≤ H) (π : ↥H →* R) (ρ : ↥A →* R), (∀ a : ↥A, π ⟨(a : G), hAH a.2⟩ = ρ a) →
    IsPGroup 3 A → π.ker ≤ Subgroup.center ↥H → ¬ 3 ∣ Nat.card π.ker →
    ∀ (X : Subgroup ↥H) (φ : MulAut ↥A),
      φ ∈ ggAutomizer (X.map H.subtype) A ↔
        ∃ y ∈ X.map π, ∀ a : ↥A, ρ (φ a) = y * ρ a * y⁻¹

end CoverComponents

end

end CFSG.StandardType.GGQ2Frame
