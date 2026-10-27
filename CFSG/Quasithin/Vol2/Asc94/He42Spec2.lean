module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

structure WSpec (S : HeSetup G) (y₁ y₂ l₁ l₂ : G) : Prop where
  mem₁ : l₁ ∈ S.L1
  mem₂ : l₂ ∈ S.L2
  sq₁ : l₁ * l₁ = 1
  sq₂ : l₂ * l₂ = 1
  nmem₁ : l₁ ∉ S.K
  nmem₂ : l₂ ∉ S.K
  cent₁ : l₁ * y₁ = y₁ * l₁
  cent₂ : l₂ * y₂ = y₂ * l₂
  inv₁ : l₁ * (y₁ * y₂⁻¹) * l₁⁻¹ = (y₁ * y₂⁻¹)⁻¹
  inv₂ : l₂ * (y₁ * y₂⁻¹) * l₂⁻¹ = (y₁ * y₂⁻¹)⁻¹

namespace HeSetup

variable (S : HeSetup G)

@[expose] def StepZmat (y₁ y₂ : G) : Prop :=
  (∀ y ∈ ({y₁, y₂, y₁ * y₂⁻¹} : Set G), ∀ z ∈ S.Z, y * z * y⁻¹ ∈ S.Z) ∧
    (∀ z ∈ S.Z, y₁ * z * y₁⁻¹ * z⁻¹ ∈ S.B → z ∈ S.B) ∧
    (∀ z ∈ S.Z, y₂ * z * y₂⁻¹ * z⁻¹ ∈ S.B → z ∈ S.B) ∧
    ∃ z ∈ S.Z, (y₁ * y₂⁻¹) * z * (y₁ * y₂⁻¹)⁻¹ ≠ z

@[expose] def StepComm (y₁ y₂ : G) : Prop :=
  (∀ l ∈ S.L1, y₁ * l * y₁⁻¹ * l⁻¹ ∈ S.A) ∧ ∀ l ∈ S.L2, y₂ * l * y₂⁻¹ * l⁻¹ ∈ S.A'

@[expose] def StepKer : Prop :=
  ∀ g ∈ S.L, (∀ x ∈ S.L, x⁻¹ * g * x ∈ S.L1) → g ∈ S.B

end HeSetup

end CFSG.Quasithin.A94.He42
