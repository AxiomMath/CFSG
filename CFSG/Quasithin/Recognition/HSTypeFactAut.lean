module

public import CFSG.Quasithin.Recognition.M22UniqueSystem

public section

namespace CFSG.Quasithin.HSType

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

@[expose] def FactAutL34 : Prop :=
  ∀ β : ↥(stabilizer M22 (0 : Fin 22)) ≃* ↥(stabilizer M22 (0 : Fin 22)),
    (∀ x, β (β x) = x) →
    (∀ x : ↥(stabilizer M22 (0 : Fin 22)),
      (x : M22) ∈ m22TwoStab ↔ ((β x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab) →
      (∃ d : ↥(stabilizer M22 (0 : Fin 22)), (d : M22) ∈ m22TwoStab ∧
          ∀ x, β x = d * x * d⁻¹) ∨
        ∃ w : ↥(stabilizer M22 (0 : Fin 22)), orderOf w = 7 ∧ β w = w

end CFSG.Quasithin.HSType
