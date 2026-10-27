module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Tilde19

variable {W : Type} [CommGroup W]

@[expose] def Uniq19 (X : Subgroup (MulAut W)) (Δt : Set (Subgroup W)) : Prop :=
  ∀ t₁ ∈ X, ∀ t₂ ∈ X, t₁ * t₁ = 1 → t₂ * t₂ = 1 → t₁ * t₂ = t₂ * t₁ → t₁ ≠ 1 → t₂ ≠ 1 →
    ∀ I ∈ Δt, I ≤ fixV (Subgroup.zpowers t₁) → I ≤ fixV (Subgroup.zpowers t₂) → t₁ = t₂

@[expose] def Two19 (X : Subgroup (MulAut W)) : Prop :=
  ∀ E : Subgroup (MulAut W), E ≤ X → (∀ e ∈ E, e * e = 1) → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
    3 ≤ rk ↥E → ∃ F₁ F₂ : Subgroup (MulAut W), F₁ ≤ E ∧ F₂ ≤ E ∧ F₁ ≠ F₂ ∧
      E3.mQuot E F₁ = 1 ∧ E3.mQuot E F₂ = 1 ∧ fixV F₁ ≠ fixV E ∧ fixV F₂ ≠ fixV E

end Tilde19

section Facts19

variable {G : Type} [Group G] [Finite G]

@[expose] def Unique19 (D : Data G) (V : Subgroup G) (g : G) (Δ : Set (Subgroup G)) : Prop :=
  ∀ u ∈ V ⊓ conjSubgroup D.M g, ∀ z ∈ V ⊓ conjSubgroup D.M g,
    ¬ conjSubgroup V g ≤ centralizer ({u} : Set G) →
    ¬ conjSubgroup V g ≤ centralizer ({z} : Set G) →
    ∀ I ∈ deltaConj Δ g, I ≤ centralizer ({u} : Set G) → I ≤ centralizer ({z} : Set G) →
      conjSubgroup V g ⊓ centralizer ({u} : Set G) = conjSubgroup V g ⊓ centralizer ({z} : Set G)

@[expose] def Second19 (V A : Subgroup G) : Prop :=
  ∀ B U : Subgroup G, Hyperplane1618 V A B U →
    ∃ B' U' : Subgroup G, Hyperplane1618 V A B' U' ∧ B' ≠ B

end Facts19

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
