module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open

@[expose] def FactL34Parab : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 3 2 2 Q →
    ∀ S : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ →
      ∃ P₁ P₂ : Subgroup Q, P₁ ≠ P₂ ∧ P₁ ≠ ⊤ ∧ P₂ ≠ ⊤ ∧
        quasithinIsCComponent P₁ P₁ ∧ quasithinIsCComponent P₂ P₂ ∧
        quasithinIsCComponent (⊤ : Subgroup Q) ⊤ ∧
        S ≤ Subgroup.normalizer (P₁ : Set Q) ∧ S ≤ Subgroup.normalizer (P₂ : Set Q) ∧
        P₁ ⊔ P₂ = ⊤ ∧ Subgroup.normalizer (S : Set Q) ≤ P₁ ⊓ P₂ ∧
        ∀ P : Subgroup Q, P ≠ ⊥ → ⁅P, P⁆ = P → S ≤ Subgroup.normalizer (P : Set Q) →
          P = P₁ ∨ P = P₂ ∨ P = ⊤

@[expose] def FactPGL34Levi : Prop :=
  ∀ (R : Type) [Group R] [Finite R],
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (R ≃* (Matrix.GeneralLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)))) →
    ∀ S P₁ P₂ : Subgroup R, QuasithinUnique.IsSylowTwoOf S ⊤ → P₁ ≠ P₂ → P₁ ≠ ⊥ → P₂ ≠ ⊥ →
      ⁅P₁, P₁⁆ = P₁ → ⁅P₂, P₂⁆ = P₂ → P₁ ≠ ⁅(⊤ : Subgroup R), ⊤⁆ → P₂ ≠ ⁅(⊤ : Subgroup R), ⊤⁆ →
      S ≤ Subgroup.normalizer (P₁ : Set R) → S ≤ Subgroup.normalizer (P₂ : Set R) →
      ∀ x : R, x ∈ Subgroup.normalizer (S : Set R) → orderOf x = 3 →
        x ∈ sectionCentralizer P₁ (pCoreOf 2 P₁) → x ∉ sectionCentralizer P₂ (pCoreOf 2 P₂)

end CFSG.Quasithin.Vol2.Ch11.SecS
