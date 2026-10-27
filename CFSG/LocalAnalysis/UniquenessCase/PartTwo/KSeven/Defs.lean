module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open Subgroup

@[expose] def fixedBy {J : Type*} [Group J] (W : Subgroup (MulAut J)) : Subgroup J where
  carrier := {j | ∀ w ∈ W, w j = j}
  one_mem' := fun w _ => map_one w
  mul_mem' := fun {a b} ha hb w hw => by rw [map_mul, ha w hw, hb w hw]
  inv_mem' := fun {a} ha w hw => by rw [map_inv, ha w hw]

theorem mem_fixedBy {J : Type*} [Group J] {W : Subgroup (MulAut J)} {j : J} :
    j ∈ fixedBy W ↔ ∀ w ∈ W, w j = j := Iff.rfl

@[expose] def SevenFree (J : Type) [Group J] : Prop :=
  ∀ W : Subgroup (MulAut J), IsPGroup 7 W → W ≠ ⊥ → ∀ Z : Sylow 3 J,
    (∀ w ∈ W, ∀ z ∈ (Z : Subgroup J), w z = z) →
      normalizer ((Z : Subgroup J) : Set J) ⊔ fixedBy W = ⊤

@[expose] def StepConcl (Good : ∀ (J : Type) [Group J], Prop) {J : Type} [Group J]
    (W : Subgroup (MulAut J)) (Z : Subgroup J) : Prop :=
  Good ↥⁅fixedBy W, fixedBy W⁆ ∧ Z ≤ ⁅fixedBy W, fixedBy W⁆ ∧
    normalizer (Z : Set J) ⊔ ⁅fixedBy W, fixedBy W⁆ = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
