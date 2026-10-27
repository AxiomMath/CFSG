module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlat

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint

@[expose] def SporKRestControlsAt {K : Type} [Group K] (x : K) (Y : Subgroup K) : Prop :=
  ∀ g : K, g⁻¹ * x * g ∈ Y → g ∈ Y

@[expose] def SporKRestControls {K : Type} [Group K] (E Y : Subgroup K) : Prop :=
  ∀ e ∈ E, e ≠ 1 → SporKRestControlsAt e Y

@[expose] def SporKRestGenerating {K : Type} [Group K] (p : ℕ) (x : K) : Prop :=
  ∀ Y : Subgroup K, (∃ S : Sylow p K, (S : Subgroup K) ≤ Y) → SporKRestControlsAt x Y → Y = ⊤

@[expose] def SporKRestCover (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ E : Subgroup K, IsElemAbelian p E → Nat.card E = p ^ 2 →
    ∃ x ∈ E, x ≠ 1 ∧ SporKRestGenerating p x

@[expose] def SporKRestUnmarked (X : Type) [Group X] : Prop :=
  ∀ C : Subgroup (X ⧸ CFSG.pCore 2 X), IsComponentOf C ⊤ →
    ¬ LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True)

@[expose] def SporKRestCoverOrUnmarked (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ E : Subgroup K, IsElemAbelian p E → Nat.card E = p ^ 2 →
    (∃ x ∈ E, x ≠ 1 ∧ SporKRestGenerating p x) ∨
    (∀ Y : Subgroup K, Y ≠ ⊤ → (∃ S : Sylow p K, (S : Subgroup K) ≤ Y) →
      SporKRestControls E Y → SporKRestUnmarked ↥Y)

@[expose] def SporKRestFi22Exc (K : Type) [Group K] : Prop :=
  ∀ E : Subgroup K, IsElemAbelian 5 E → Nat.card E = 25 →
    ∀ Y : Subgroup K, Y ≠ ⊤ → (∃ S : Sylow 5 K, (S : Subgroup K) ≤ Y) → SporKRestControls E Y →
      ∀ C : Subgroup K, IsComponentOf C Y →
        LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1

end CFSG.StandardType.SporadicShape
