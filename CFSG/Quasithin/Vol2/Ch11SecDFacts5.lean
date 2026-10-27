module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11StatementsH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def FactM2Case1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L₁ R : Subgroup G) (n : ℕ),
    (List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K))) →
    Case11_1_2One K →
    (∃ p : ℕ, p.Prime ∧ IsPGroup p ↥(CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))) →
    L₁ ≤ K → ⁅L₁, L₁⁆ = L₁ →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    IsPGroup 2 R → R ≤ Subgroup.normalizer (K : Set G) → R ≤ Subgroup.normalizer (L₁ : Set G) →
    ⁅R, L₁⁆ ≤ pCoreOf 2 L₁ →
    ∀ A : Subgroup G, A ≤ R → IsElemAbelian 2 A →
      E3.mQuot A (A ⊓ sectionCentralizer K (pCoreOf 2 K)) ≤ 1

@[expose] def FactM2Case1Prime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L₁ R : Subgroup G) (n p : ℕ),
    (List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K))) →
    Case11_1_2One K → ⁅K, K⁆ = K → L₁ ≤ K → ⁅L₁, L₁⁆ = L₁ →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    IsPGroup 2 R → R ≤ Subgroup.normalizer (K : Set G) → R ≤ Subgroup.normalizer (L₁ : Set G) →
    ⁅R, L₁⁆ ≤ pCoreOf 2 L₁ → p.Prime →
    ∀ A : Subgroup G, A ≤ R → IsElemAbelian 2 A →
      E3.mQuot A (A ⊓ sectionCentralizer (oTwoPrime K p ⊔ L₁) (pCoreOf 2 K)) ≤ 1

@[expose] def FactCase1PrimeAct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L₁ : Subgroup G) (n p : ℕ),
    (List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K))) →
    Case11_1_2One K → ⁅K, K⁆ = K → L₁ ≤ K → ⁅L₁, L₁⁆ = L₁ →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    p.Prime → ¬ oTwoPrime K p ≤ pCoreOf 2 K →
    (∀ y ∈ oTwoPrime K p ⊔ L₁, (∀ x ∈ oTwoPrime K p, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 K) →
      y ∈ oTwoPrime K p) ∧
    ∀ a : G, a ∈ Subgroup.normalizer (K : Set G) → (∃ e : ℕ, a ^ 2 ^ e = 1) →
      (∀ x ∈ oTwoPrime K p, ∀ l ∈ L₁,
        (a * x * a⁻¹ * x⁻¹) * l * (a * x * a⁻¹ * x⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 K) →
      ∀ x ∈ oTwoPrime K p, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 K

end CFSG.Quasithin.Vol2.Ch11.SecD
