module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

section Vocabulary

@[expose] def IsZ3TimesPOnePlusTwo (X : Type) [Group X] : Prop :=
  ∃ (H : Type) (_ : Group H), IsPOnePlusTwo 3 H ∧ Nonempty (X ≃* Multiplicative (ZMod 3) × H)

@[expose] def IsZ3WrZ3 (X : Type) [Group X] : Prop :=
  Nat.card X = 81 ∧ ∃ (z : Fin 3 → X) (b : X), (∀ i, z i ^ 3 = 1) ∧
    (∀ i j, Commute (z i) (z j)) ∧ b ^ 3 = 1 ∧ (∀ i, b * z i * b⁻¹ = z (i + 1)) ∧
    Subgroup.closure (Set.range z ∪ {b}) = ⊤

end Vocabulary

@[expose] def W4Lem13_1 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ t : MulAut W, orderOf t = 2 → rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 →
      ∀ (p : ℕ) (P : Subgroup (MulAut W)), p.Prime → IsPGroup p ↥P → P ≠ ⊥ →
        (∀ x ∈ P, t * x * t⁻¹ ∈ P) → ⁅P, Subgroup.zpowers t⁆ = P →
          p ≤ 7 ∧ ((3 < p ∨ InducesTransvection t ⊤) → Nat.card P = p)

@[expose] def W4Lem13_2Min : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ t : MulAut W, orderOf t = 2 → rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 →
      ∀ (p : ℕ) (P : Subgroup (MulAut W)), p.Prime → IsPGroup p ↥P → P ≠ ⊥ →
        (∀ x ∈ P, t * x * t⁻¹ ∈ P) → ⁅P, Subgroup.zpowers t⁆ = P →
          (∀ U : Subgroup W, StableUnder (P ⊔ Subgroup.zpowers t) U →
            (∀ y ∈ P ⊔ Subgroup.zpowers t, (∀ u ∈ U, y u = u) → y = 1) → U = ⊤) →
          (IsCyclic ↥P ∧ Nat.card P ≤ 9) ∨
          (∃ n : ℕ, n ≤ 3 ∧ IsElemAbelianOfRank 3 n ↥P) ∨
          (IsPOnePlusTwo 3 ↥P ∧ rk ↥(commSub ⊤ P) = 6) ∨
          ((IsZ3TimesPOnePlusTwo ↥P ∨ IsZ3WrZ3 ↥P) ∧
            rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 ∧
            ∃! Q : Subgroup (MulAut W), Q ≤ P ∧ IsPOnePlusTwo 3 ↥Q ∧ rk ↥(commSub ⊤ Q) = 6)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
