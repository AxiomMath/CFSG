module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.StandardType

@[expose] def ggFixSub {X : Type*} [Group X] (e : MulAut X) : Subgroup X where
  carrier := {l | e l = l}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  one_mem' := map_one e
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv, ha]

@[simp] theorem mem_ggFixSub {X : Type*} [Group X] {e : MulAut X} {l : X} :
    l ∈ ggFixSub e ↔ e l = l :=
  Iff.rfl

end CFSG.StandardType

end
