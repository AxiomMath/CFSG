module

public import CFSG.RankThree.PartTwo.Sec21.Item22Statements
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Inspection223 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A B K : Subgroup G) (m : ℕ),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 3 ^ 4 →
    A ≤ Subgroup.normalizer (X : Set G) →
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 →
    (∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal) →
    B ≤ A → Nat.card B = 3 ^ 3 → K ≤ X → K ≤ Subgroup.centralizer (B : Set G) →
    (∀ y ∈ X ⊓ Subgroup.centralizer (B : Set G), ∀ k ∈ K, y * k * y⁻¹ ∈ K) →
    Nonempty (K ≃* projSL 2 (GaloisField 2 m)) → 1 < m → Odd m →
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 m)

@[expose] def U4TorusBlocks : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T B₁ B₂ K₁ K₂ : Subgroup G) (m : ℕ),
    Nonempty (X ≃* projSU 4 2 m) → 1 < m → Odd m →
    T ≤ X → CFSG.Assembly.IsElemAbelian 3 T → Nat.card T = 3 ^ 3 →
    B₁ ≤ T → B₂ ≤ T → Nat.card B₁ = 3 ^ 2 → Nat.card B₂ = 3 ^ 2 → B₁ ≠ B₂ →
    K₁ ≤ X → K₂ ≤ X →
    K₁ ≤ Subgroup.centralizer (B₁ : Set G) → K₂ ≤ Subgroup.centralizer (B₂ : Set G) →
    (∀ y ∈ X ⊓ Subgroup.centralizer (B₁ : Set G), ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₁) →
    (∀ y ∈ X ⊓ Subgroup.centralizer (B₂ : Set G), ∀ k ∈ K₂, y * k * y⁻¹ ∈ K₂) →
    Nonempty (K₁ ≃* projSL 2 (GaloisField 2 m)) → Nonempty (K₂ ≃* projSL 2 (GaloisField 2 m)) →
    ∀ ρ₁ ρ₂ : MulAut T, IsReflectionOn ρ₁ → IsReflectionOn ρ₂ →
      fixedInG T ρ₁ = B₁ → fixedInG T ρ₂ = B₂ →
      (commOf ρ₁).map T.subtype ≤ K₁ → (commOf ρ₂).map T.subtype ≤ K₂ →
      (ρ₁ * ρ₂ = ρ₂ * ρ₁ → ⁅K₁, K₂⁆ = ⊥) ∧
      (ρ₁ * ρ₂ ≠ ρ₂ * ρ₁ → Nonempty ((K₁ ⊔ K₂ : Subgroup G) ≃* SU3 m) ∧
        Nonempty (Subgroup.closure {ρ₁, ρ₂} ≃* Equiv.Perm (Fin 3)))

end CFSG.RankThree.PartTwo.Sec21
