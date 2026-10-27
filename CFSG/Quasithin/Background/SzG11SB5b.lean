module

public import CFSG.Quasithin.Background.SzG11SStmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

@[expose] def G115bPart1 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G111Hyp B Γ v₁ W X X₀ → IsIrr Γ ⊤ →
      (∃ x ∈ X, x ≠ 1 ∧ ∀ f ∈ fittingOf Γ, x * f = f * x) →
      ∃ L : Subgroup (GLV V), IsComponentOf L Γ ∧ ∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x

@[expose] def G115bPart2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11Cx B Γ v₁ W X X₀ → IsIrr Γ ⊤ →
      (∃ L : Subgroup (GLV V), IsComponentOf L Γ ∧ ∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x) →
      ∃ L : Subgroup (GLV V), IsComponentOf L Γ ∧ (∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x) ∧
        numConjugates Γ L ≤ 2

theorem g115b_of_parts (h1 : G115bPart1) (h2 : G115bPart2) : G115bStmt := by
  intro V _ _ _ B Γ v₁ W X X₀ cx hirr hx
  exact h2 V B Γ v₁ W X X₀ cx hirr (h1 V B Γ v₁ W X X₀ cx.hyp hirr hx)

end SzG11S

end G11

end CFSG.Quasithin
