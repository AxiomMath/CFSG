module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def FactG2AdjointOrder : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    Nat.card (AdjointQuotient .G2 K) = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))

@[expose] def FactG2DerivedTwoOrder : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ = 6048

@[expose] def FactL34 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ f : Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2),
      ¬ Function.Surjective f

@[expose] def FactNoGraphSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π →
      ∀ Tb : Subgroup (MulAut W), (∀ t ∈ Tb, ∀ h ∈ H, t * h * t⁻¹ ∈ H) →
        H13.NoGraphAutomorphism π Tb

@[expose] def FactNoGraphSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π → (∀ h ∈ H, ∀ z ∈ Z, h z = z) →
      ∀ Tb : Subgroup (MulAut W), (∀ t ∈ Tb, ∀ h ∈ H, t * h * t⁻¹ ∈ H) →
        (∀ t ∈ Tb, ∀ w : W, w ∈ Z ↔ t w ∈ Z) →
        NoGraphAutomorphismSp4 π Tb

structure Facts02 : Prop where
  g2Adjoint : FactG2AdjointOrder
  g2Derived : FactG2DerivedOrder
  g2DerivedTwo : FactG2DerivedTwoOrder
  l34 : FactL34
  noGraphSL3 : FactNoGraphSL3
  noGraphSp4 : FactNoGraphSp4

end CFSG.Quasithin.Vol2.Ch11.SecA
