module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecSBridge

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint

@[expose] def FactL34NoE9 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 3 2 2 Q →
    ∀ S : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ →
      ∀ B₁ B₂ : Subgroup Q, B₁ ≠ B₂ → B₁ ≠ ⊥ → B₂ ≠ ⊥ → B₁ ≠ ⊤ → B₂ ≠ ⊤ →
        ⁅B₁, B₁⁆ = B₁ → ⁅B₂, B₂⁆ = B₂ →
        S ≤ Subgroup.normalizer (B₁ : Set Q) → S ≤ Subgroup.normalizer (B₂ : Set Q) →
        ∀ E : Subgroup Q, E ≤ Subgroup.normalizer (B₁ : Set Q) →
          E ≤ Subgroup.normalizer (B₂ : Set Q) → Nat.card ↥E ≠ 9

@[expose] def FactParabGen : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Shape4 Q →
    ∀ S : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ →
      ∀ B₁ B₂ : Subgroup Q, B₁ ≠ B₂ → B₁ ≠ ⊥ → B₂ ≠ ⊥ → ⁅B₁, B₁⁆ = B₁ → ⁅B₂, B₂⁆ = B₂ →
        S ≤ Subgroup.normalizer (B₁ : Set Q) → S ≤ Subgroup.normalizer (B₂ : Set Q) →
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
          Nonempty (↥B₁ ⧸ CFSG.pCore 2 ↥B₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
          Nonempty (↥B₂ ⧸ CFSG.pCore 2 ↥B₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
          B₁ ⊔ B₂ = ⊤

end CFSG.Quasithin.Vol2.Ch11.SecS
