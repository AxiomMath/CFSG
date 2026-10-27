module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

section Vocabulary

variable {W : Type*} [Group W]

@[expose] def commS (S : Subgroup (MulAut W)) (U : Subgroup W) : Subgroup W :=
  Subgroup.closure {w | ∃ s ∈ S, ∃ u ∈ U, s u * u⁻¹ = w}

@[expose] def LineFacts (H : Subgroup (MulAut W)) (Z U₂ : Subgroup W) : Prop :=
  (∀ s ∈ pCoreOf 2 (perfectCore (H ⊓ stabW U₂)), ∀ u ∈ U₂, s u = u) ∧
  (∃ s ∈ perfectCore (H ⊓ stabW U₂), ∃ u ∈ U₂, s u ≠ u) ∧
  (∀ u ∈ U₂, (∀ s ∈ perfectCore (H ⊓ stabW U₂), s u = u) ↔ u ∈ Z) ∧
  U₂ = commS (perfectCore (H ⊓ stabW U₂)) U₂ ⊔ Z ∧
  ∀ φ ψ : W → W, (∀ u ∈ U₂, φ u ∈ U₂) → (∀ u ∈ U₂, ψ u ∈ U₂) →
    (∀ u ∈ U₂, ∀ v ∈ U₂, φ (u * v) = φ u * φ v) → (∀ u ∈ U₂, ∀ v ∈ U₂, ψ (u * v) = ψ u * ψ v) →
    (∀ s ∈ perfectCore (H ⊓ stabW U₂), ∀ u ∈ U₂, φ (s u) = s (φ u)) →
    (∀ s ∈ perfectCore (H ⊓ stabW U₂), ∀ u ∈ U₂, ψ (s u) = s (ψ u)) →
    ∀ y ∈ commS (perfectCore (H ⊓ stabW U₂)) U₂, φ (ψ y) = ψ (φ y)

@[expose] def PerfCentFacts (H : Subgroup (MulAut W)) (Z U₂ : Subgroup W) : Prop :=
  ∀ K : Subgroup (MulAut W), ⁅K, K⁆ = K → (∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) →
    K ≤ stabW Z → K ≤ stabW U₂ →
    (∀ k ∈ K, ∀ s ∈ perfectCore (H ⊓ stabW U₂),
      k * s * k⁻¹ * s⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ stabW U₂))) →
    ∀ k ∈ K, ∀ w : W, k w = w

end Vocabulary

@[expose] def FactLineSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π → (∀ h ∈ H, ∀ z ∈ Z, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ → LineFacts H Z U₂

@[expose] def FactLineSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π → (∀ h ∈ H, ∀ z ∈ Z, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ →
        LineFacts H Z U₂ ∧ (commV H = ⊤ → PerfCentFacts H Z U₂)

@[expose] def FactLineG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      (∀ h ∈ H, ∀ z ∈ Z, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ →
        LineFacts H Z U₂ ∧ (commV H = ⊤ → PerfCentFacts H Z U₂)

end CFSG.Quasithin.Vol2.Ch11.SecA
