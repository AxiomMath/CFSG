module

public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F6

section Cases

variable {D : Type} [Group D]

@[expose] def IsF618CaseRestCat (H₁ H₂ : Subgroup D) : Prop :=
  IsF618CaseThree H₁ H₂ ∨ IsF618CaseFour H₁ H₂ ∨ IsF618CaseFive H₁ H₂ ∨ IsF618CaseSix H₁ H₂ ∨
    IsF618CaseSeven H₁ H₂ ∨ IsF618CaseEightCat H₁ H₂ ∨ IsF618CaseNineCat H₁ H₂ ∨
    IsF618CaseTen H₁ H₂ ∨ IsF618CaseEleven H₁ H₂ ∨ IsF618CaseTwelve H₁ H₂ ∨
    IsF618CaseThirteen H₁ H₂

theorem isF618CaseRestCat_of_oriented {H₁ H₂ : Subgroup D} (h : IsF618CaseOrientedCat H₁ H₂)
    (h1 : ¬ IsF618CaseOne H₁ H₂) (h2 : ¬ IsF618CaseTwo D) : IsF618CaseRestCat H₁ H₂ := by
  rcases h with h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact h

end Cases

@[expose] def InspF618Rest : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (H₁ H₂ : Subgroup D),
    (IsF618CaseRestCat H₁ H₂ → CFSG.IsQuasisimple ↥(perfectCore (⊤ : Subgroup D))) ∧
    ((IsF618CaseThree H₁ H₂ ∨ IsF618CaseFour H₁ H₂ ∨ IsF618CaseFive H₁ H₂) →
      ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
        IsL2 p 1 (↥(perfectCore (⊤ : Subgroup D)) ⧸
          Subgroup.center ↥(perfectCore (⊤ : Subgroup D)))) ∧
    (IsF618CaseSix H₁ H₂ →
      Nonempty (↥(perfectCore (⊤ : Subgroup D)) ⧸
          Subgroup.center ↥(perfectCore (⊤ : Subgroup D)) ≃* ↥(alternatingGroup (Fin 6))) ∨
        ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ e ≤ 2 ∧ (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧
          IsL2 p e (↥(perfectCore (⊤ : Subgroup D)) ⧸
            Subgroup.center ↥(perfectCore (⊤ : Subgroup D)))) ∧
    (IsF618CaseSeven H₁ H₂ →
      Nonempty (↥(perfectCore (⊤ : Subgroup D)) ⧸
        Subgroup.center ↥(perfectCore (⊤ : Subgroup D)) ≃* ↥(alternatingGroup (Fin 7)))) ∧
    (IsF618CaseEightCat H₁ H₂ →
      Nonempty (↥(perfectCore (⊤ : Subgroup D)) ⧸
          Subgroup.center ↥(perfectCore (⊤ : Subgroup D)) ≃* ↥(alternatingGroup (Fin 6))) ∨
        ∃ p : ℕ, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
          IsL2 p 2 (↥(perfectCore (⊤ : Subgroup D)) ⧸
            Subgroup.center ↥(perfectCore (⊤ : Subgroup D)))) ∧
    (IsF618CaseNineCat H₁ H₂ →
      Nonempty (↥(perfectCore (⊤ : Subgroup D)) ⧸
          Subgroup.center ↥(perfectCore (⊤ : Subgroup D)) ≃* ↥(alternatingGroup (Fin 7))) ∨
        ∃ p : ℕ, p.Prime ∧ (p % 24 = 5 ∨ p % 24 = 19) ∧
          IsL2 p 2 (↥(perfectCore (⊤ : Subgroup D)) ⧸
            Subgroup.center ↥(perfectCore (⊤ : Subgroup D)))) ∧
    ((IsF618CaseTen H₁ H₂ ∨ IsF618CaseEleven H₁ H₂) →
      ∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧
        IsSLEps3 p (↥(perfectCore (⊤ : Subgroup D)) ⧸
          Subgroup.center ↥(perfectCore (⊤ : Subgroup D)))) ∧
    ((IsF618CaseTwelve H₁ H₂ ∨ IsF618CaseThirteen H₁ H₂) →
      IsM12 (↥(perfectCore (⊤ : Subgroup D)) ⧸
        Subgroup.center ↥(perfectCore (⊤ : Subgroup D))))

end F6

end CFSG.Quasithin
