module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure315Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.GorensteinWalter
open scoped Pointwise

@[expose] def burnsideA315y_PGL2Statement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ B D : Subgroup (PGL2 (ZMod p)),
    IsMulCommutative ↥B → Odd (Nat.card ↥B) → IsPGroup 2 ↥D →
    Nat.card ↥D = 2 ^ (Nat.card (PGL2 (ZMod p))).factorization 2 →
    (B : Set (PGL2 (ZMod p))) * (D : Set (PGL2 (ZMod p))) =
      (D : Set (PGL2 (ZMod p))) * (B : Set (PGL2 (ZMod p))) →
    IsCyclic ↥B ∧
    (((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
          ((Nat.card ↥B : ℕ) : ℤ) ∣ (p : ℤ) - ε) ∧
        ∃ d ∈ D, d ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range ∧
          ∀ x ∈ B, d * x * d⁻¹ = x⁻¹) ∨
     ((p % 8 = 3 ∨ p % 8 = 5) ∧ Nat.card ↥B = 3 ∧ ∃ d ∈ D, ∀ x ∈ B, d * x * d⁻¹ = x⁻¹))

@[expose] def burnsideA315y_StepsStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (K M B S : Subgroup X), Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) →
    K ≤ M → M ≤ Subgroup.normalizer (K : Set X) →
    (∀ c ∈ M ⊓ Subgroup.centralizer (K : Set X), ∀ m ∈ M, c * m = m * c) →
    B ≤ M → IsMulCommutative ↥B → Odd (Nat.card ↥B) →
    (∀ b ∈ B, ∃ k ∈ K, ∃ c ∈ M ⊓ Subgroup.centralizer (K : Set X), b = k * c) →
    S ≤ M → IsPGroup 2 ↥S → (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X) →
    Nat.card ↥(S ⊓ K) = 2 ^ (Nat.card ↥K).factorization 2 →
    Nat.card ↥S = 2 ^ (Nat.card (PGL2 (ZMod p))).factorization 2 *
      Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set X)) →
    B = (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) ∧ IsCyclic ↥(B ⊓ K) ∧
    (((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
          ((Nat.card ↥(B ⊓ K) : ℕ) : ℤ) ∣ (p : ℤ) - ε) ∧
        ∃ t ∈ S ⊓ K, ∀ x ∈ B ⊓ K, t * x * t⁻¹ = x⁻¹) ∨
     ((p % 8 = 3 ∨ p % 8 = 5) ∧ Nat.card ↥(B ⊓ K) = 3 ∧
        ∃ t ∈ S ⊓ Subgroup.normalizer (B : Set X), ∀ x ∈ B ⊓ K, t * x * t⁻¹ = x⁻¹))

@[expose] def burnsideA315y_FittingStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (B S : Subgroup X), IsMulCommutative ↥B → Odd (Nat.card ↥B) →
    IsPGroup 2 ↥S → (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X) →
    (∃ R : Subgroup X, R ≤ S ∧ R ≠ ⊥ ∧ B ≤ Subgroup.normalizer (R : Set X) ∧
      S ≤ Subgroup.normalizer (R : Set X)) ∨ S ≤ Subgroup.normalizer (B : Set X)

@[expose] def burnsideA315y_CartanStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → ∀ (L I U Q : Subgroup X),
    L ≤ I → CFSG.Quasithin.A315.IsSylowOf p U L → ¬ p ∣ L.relIndex I →
    Q ≤ I → Q ≤ Subgroup.normalizer (U : Set X) → ¬ p ∣ Nat.card ↥Q →
    ∃ H : Subgroup X, CFSG.Quasithin.A315.IsCartan p U I H ∧ Q ≤ H

@[expose] def burnsideA315y_ModelConclusion (X : Type) [Group X] (δ : Bool) (p : ℕ)
    (L B S : Subgroup X) : Prop :=
  (δ = true ∧ B ≤ L ∧ CFSG.Quasithin.IsElemAbelianOfRank p 2 ↥B ∧
      S ≤ Subgroup.normalizer (B : Set X) ∧ B ≠ ⊥ ∧
      ∀ C : Subgroup X, C ≤ B → S ≤ Subgroup.normalizer (C : Set X) → C = ⊥ ∨ C = B) ∨
  (∃ K : Subgroup X, K ≤ L ∧ CFSG.Quasithin.IsSL2 p ↥K ∧
      B = (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) ∧
      IsCyclic ↥(B ⊓ K) ∧ IsCyclic ↥(B ⊓ Subgroup.centralizer (K : Set X)) ∧
      (∃ H U : Subgroup X, CFSG.Quasithin.A315.IsSylowOf p U L ∧
        CFSG.Quasithin.A315.IsCartan p U (L ⊔ B) H ∧ B ⊓ Subgroup.centralizer (K : Set X) ≤ H) ∧
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) ∣ (if δ then p - 1 else p + 1) ∧
      (((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
          ((Nat.card ↥(B ⊓ K) : ℕ) : ℤ) ∣ (p : ℤ) - ε) ∧
        CFSG.Quasithin.A315.InvertedIn (B ⊓ K) (S ⊓ K)) ∨
       ((p % 8 = 3 ∨ p % 8 = 5) ∧ Nat.card ↥(B ⊓ K) = 3 ∧
        CFSG.Quasithin.A315.InvertedIn (B ⊓ K) (S ⊓ Subgroup.normalizer (B : Set X) ⊓
          Subgroup.centralizer ((B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) : Set X)))))

end CFSG.ASVolI
