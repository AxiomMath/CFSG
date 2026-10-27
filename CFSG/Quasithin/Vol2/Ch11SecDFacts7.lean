module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def FactCase1NormL1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L₁ N : Subgroup G) (n : ℕ),
    (List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K))) →
    Case11_1_2One K → ⁅K, K⁆ = K → L₁ ≤ K → ⁅L₁, L₁⁆ = L₁ →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    N ≤ K → K ≤ Subgroup.normalizer (N : Set G) → N ≤ Subgroup.normalizer (L₁ : Set G) →
      N ≤ sectionCentralizer K (pCoreOf 2 K)

@[expose] def FactCase1GL8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (n : ℕ),
    (List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K))) →
    Case11_1_2One K → ⁅K, K⁆ = K →
    ∀ (E : Type) [Group E] [Finite E], (∀ a b : E, a * b = b * a) → (∀ e : E, e ^ 2 = 1) →
      Nat.card E ≤ 2 ^ 8 → ∀ ρ : ↥K →* MulAut E,
        ¬ ∀ k : ↥K, ρ k = 1 → (k : G) ^ 2 ∈ sectionCentralizer K (pCoreOf 2 K)

end CFSG.Quasithin.Vol2.Ch11.SecD
