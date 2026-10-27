module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.F112R.St84

open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] def IsNatSecOf (L E N : Subgroup G) {F : Type*} [Field F] (α : ↥L →* SL(2, F)) :
    Prop :=
  ∃ β : ↥E →* Multiplicative (Fin 2 → F), Function.Surjective β ∧ β.ker = N.subgroupOf E ∧
    ∀ ℓ : ↥L, ∀ u v : ↥E, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

end CFSG.Quasithin.F112R.St84

end
