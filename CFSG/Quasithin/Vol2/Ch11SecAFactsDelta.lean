module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def DeltaFacts {W : Type*} [Group W] (H P : Subgroup (MulAut W)) (q : ℕ)
    (U₁ U₂ U₃ : Subgroup W) : Prop :=
  (∀ u ∈ U₃, (∀ s ∈ pCoreOf 2 (perfectCore (H ⊓ stabW U₁)), s u = u) ↔ u ∈ U₁) ∧
  (∀ R : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf R (perfectCore (H ⊓ stabW U₁)) →
    R ≤ P → ∀ U : Subgroup W, U₁ ≤ U → U ≤ U₃ → U₁.relIndex U = q → R ≤ stabW U → U = U₂) ∧
  (⨆ g ∈ perfectCore (H ⊓ stabW U₁), perfectCore (H ⊓ stabW (U₂.map g.toMonoidHom))) = H

@[expose] def FactDeltaSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π → (∀ h ∈ H, ∀ z ∈ Z, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ U₂ U₃ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ → IsFlagW H P Z (2 ^ n) 2 U₂ →
        IsFlagW H P Z (2 ^ n) 3 U₃ → DeltaFacts H P (2 ^ n) U₁ U₂ U₃

@[expose] def FactDeltaG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      (∀ h ∈ H, ∀ z ∈ Z, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ U₂ U₃ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ → IsFlagW H P Z (2 ^ n) 2 U₂ →
        IsFlagW H P Z (2 ^ n) 3 U₃ → DeltaFacts H P (2 ^ n) U₁ U₂ U₃

end CFSG.Quasithin.Vol2.Ch11.SecA
