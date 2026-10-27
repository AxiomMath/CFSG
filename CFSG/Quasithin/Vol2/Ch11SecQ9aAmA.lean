module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open

@[expose] def FactG2FourLongParabolic : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsG2Over 2 Y →
    ∀ T M K V A B : Subgroup Y, QuasithinUnique.IsSylowTwoOf T ⊤ → IsMaximalTwoLocal M →
      Subgroup.normalizer (T : Set Y) ≤ M → K ≤ M → M ≤ Subgroup.normalizer (K : Set Y) →
      ⁅K, K⁆ = K →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      V ≤ M → M ≤ Subgroup.normalizer (V : Set Y) → Nat.card ↥V = 4 →
      K ≤ Subgroup.centralizer (V : Set Y) →
      A ≤ B → B ≤ pCoreOf 2 M → B ≤ Subgroup.normalizer (A : Set Y) →
      K ≤ Subgroup.normalizer (A : Set Y) → K ≤ Subgroup.normalizer (B : Set Y) → A ≠ B →
      ∀ y ∈ K, orderOf y = 3 → ∃ b ∈ B, b ∉ A ∧ y * b * y⁻¹ * b⁻¹ ∈ A

end CFSG.Quasithin.Vol2.Ch11.SecS
