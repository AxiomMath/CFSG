module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts
public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def A312A5Fact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (B L : Subgroup Y) (F : Type) [Field F] [Finite F],
    Nat.card F = 4 →
    (∃ φ : ↥B →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective φ ∧ IsPGroup 2 ↥φ.ker) →
    (B = L ∨ A312Case B L ∨ A312Nonquasi B L) → ∀ p : ℕ, p.Prime → 7 ≤ p →
      ¬ IsPSL 2 p 2 ↥L ∧ ¬ IsPSL 3 p 1 ↥L ∧ ¬ IsSL3 p ↥L ∧ ¬ IsPSU 3 p 1 ↥L ∧ ¬ IsSU3 p ↥L

@[expose] def A312L2pFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (B L : Subgroup Y) (p : ℕ), p.Prime → 11 ≤ p →
    Nonempty (↥B ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) →
    (A312Case B L ∨ A312Nonquasi B L) → IsPSL 2 p 2 ↥L

@[expose] def CartanPointFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ X : Subgroup G),
    SecD.NatSetting11 G T L I n → IsVi T L I n 1 V₁ → IsCartanX T L X →
      ∀ z ∈ V₁, z ≠ 1 → ∀ w ∈ V₁, w ≠ 1 → ∃ x ∈ X, x * z * x⁻¹ = w

@[expose] def List11_1_1TwoQuasisimpleFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → List11_1_1Two X n → CFSG.IsQuasisimple X

structure Facts42 : Prop where
  a5 : A312A5Fact
  l2p : A312L2pFact
  cartan : CartanPointFact
  twoQS : List11_1_1TwoQuasisimpleFact

end CFSG.Quasithin.Vol2.Ch11.SecE
