module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType.Triality
  CFSG.ComponentClassification.OuterAutomorphisms

section Matrix

@[expose] def GGD4NonsplitTwoLocalInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], ¬ 3 ∣ Nat.card K - 1 →
    ∀ E : Subgroup (Om8 K), IsElemAbelian 3 E → 81 ≤ Nat.card E →
      ∀ T : Subgroup (Om8 K), IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set (Om8 K)) → T = ⊥

@[expose] def GGD4NonsplitOuterInvolutionInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], ¬ 3 ∣ Nat.card K - 1 →
    ∀ E : Subgroup (Om8 K), IsElemAbelian 3 E → 81 ≤ Nat.card E →
      ∀ t : MulAut (Om8 K), t ^ 2 = 1 → t ∉ inner (Om8 K) → ∃ e ∈ E, t e ≠ e

@[expose] def GGD4GraphFieldLayerInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : Om8 K) (k : ℕ) (σ : K ≃+* K),
    (k = 1 ∨ k = 2) → AutOm.fieldAutP 4 σ ≠ 1 →
    (MulAut.conj γ * (theta ^ k * AutOm.fieldAutP 4 σ)) ^ 3 = 1 →
      ∃ x ∈ LargeEvenLayer (ggFix (MulAut.conj γ * (theta ^ k * AutOm.fieldAutP 4 σ))),
        orderOf x = 8

@[expose] def GGD4GraphLayerInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ), Nat.card K = 2 ^ f → 3 ∣ 2 ^ f - 1 →
    ∀ (γ : Om8 K) (k : ℕ), (k = 1 ∨ k = 2) → (MulAut.conj γ * theta ^ k) ^ 3 = 1 →
      (∃ x ∈ LargeEvenLayer (ggFix (MulAut.conj γ * theta ^ k)), orderOf x = 8) ∨
        LieModel (↥(LargeEvenLayer (ggFix (MulAut.conj γ * theta ^ k))) ⧸
          Subgroup.center ↥(LargeEvenLayer (ggFix (MulAut.conj γ * theta ^ k)))) .PSL 3 2 f

@[expose] def GGD4ThreeCentralizerEightInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ z x : Om8 K, z ^ 3 = 1 → z ≠ 1 → x * z = z * x → orderOf x ≠ 8

end Matrix

end CFSG.StandardType
