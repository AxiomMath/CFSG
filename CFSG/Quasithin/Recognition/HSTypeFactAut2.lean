module

public import CFSG.Quasithin.Recognition.M22UniqueSystem

public section

namespace CFSG.Quasithin.HSType

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

@[expose] def FactAutL34GraphField : Prop :=
  ∀ β : ↥(stabilizer M22 (0 : Fin 22)) ≃* ↥(stabilizer M22 (0 : Fin 22)),
    (∀ x : ↥(stabilizer M22 (0 : Fin 22)),
      ((x : M22) ∈ m22TwoStab ↔
          ((β x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab) ∧
        ((x : M22) ∈ m22PtHexStab ↔
          ((β x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab)) →
    ((∃ ℓ : ↥(stabilizer M22 (0 : Fin 22)), ∀ x, β (β x) = ℓ * x * ℓ⁻¹) →
      ∃ m : ↥(stabilizer M22 (0 : Fin 22)), (m : M22) ∈ m22TwoStab ∧
        (m : M22) ∈ m22PtHexStab ∧ ∀ x, m * β (m * β x * m⁻¹) * m⁻¹ = x) ∧
    ((∀ x, β (β x) = x) →
      ((∃ E : Subgroup ↥(stabilizer M22 (0 : Fin 22)),
          Nonempty (↥E ≃* QuaternionGroup 2) ∧ ∀ e ∈ E, β e = e) ∧
        ∃ F : Subgroup ↥(stabilizer M22 (0 : Fin 22)), Nat.card F = 9 ∧ ∀ f ∈ F, β f = f) ∨
      ∃ y : ↥(stabilizer M22 (0 : Fin 22)), (y : M22) ∈ m22TwoStab ∧
        (y : M22) ∈ m22PtHexStab ∧ orderOf y = 3 ∧ β y = y)

end CFSG.Quasithin.HSType
