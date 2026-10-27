module

public import CFSG.Quasithin.Vol2.Ch11SecSBridge
public import CFSG.Quasithin.Vol2.Ch11SecA11Concl

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint

@[expose] def FactShapeInspect : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], SecA.Concl1111 Q 2 → ¬ IsSporadic .J4 Q →
    ∀ S B₁ B₂ E : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ → B₁ ≠ B₂ →
    B₁ ≠ ⊥ → B₂ ≠ ⊥ → ⁅B₁, B₁⁆ = B₁ → ⁅B₂, B₂⁆ = B₂ →
    S ≤ Subgroup.normalizer (B₁ : Set Q) → S ≤ Subgroup.normalizer (B₂ : Set Q) →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥B₁ ⧸ CFSG.pCore 2 ↥B₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥B₂ ⧸ CFSG.pCore 2 ↥B₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    Nat.card ↥E = 9 → (∀ e ∈ E, e ^ 3 = 1) →
    E ≤ Subgroup.normalizer (B₁ : Set Q) → E ≤ Subgroup.normalizer (B₂ : Set Q) →
    E ⊓ B₁ ≠ ⊥ → E ⊓ B₂ ≠ ⊥ →
    E ⊓ sectionCentralizer B₁ (pCoreOf 2 B₁) ≠ ⊥ → E ⊓ sectionCentralizer B₂ (pCoreOf 2 B₂) ≠ ⊥ →
      Shape4 Q ∧ B₁ ⊔ B₂ = ⊤

@[expose] def FactPGL34Torus : Prop :=
  ∀ (R : Type) [Group R] [Finite R],
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (R ≃* (Matrix.GeneralLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)))) →
    ∀ S P₁ P₂ : Subgroup R, QuasithinUnique.IsSylowTwoOf S ⊤ → P₁ ≠ P₂ → P₁ ≠ ⊥ → P₂ ≠ ⊥ →
      ⁅P₁, P₁⁆ = P₁ → ⁅P₂, P₂⁆ = P₂ → P₁ ≠ ⁅(⊤ : Subgroup R), ⊤⁆ → P₂ ≠ ⁅(⊤ : Subgroup R), ⊤⁆ →
      S ≤ Subgroup.normalizer (P₁ : Set R) → S ≤ Subgroup.normalizer (P₂ : Set R) →
      ∀ E : Subgroup R, E ≤ Subgroup.normalizer (S : Set R) → Nat.card ↥E = 9 →
        E ⊓ sectionCentralizer P₂ (pCoreOf 2 P₂) ≠ ⊥

@[expose] def FactL34Levi : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 3 2 2 Q →
    ∀ S : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ →
      ∀ P : Subgroup Q, P ≠ ⊥ → P ≠ ⊤ → ⁅P, P⁆ = P → S ≤ Subgroup.normalizer (P : Set Q) →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
          Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃* Matrix.SpecialLinearGroup (Fin 2) F)

end CFSG.Quasithin.Vol2.Ch11.SecS
