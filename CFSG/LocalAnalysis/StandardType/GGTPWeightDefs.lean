module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.StandardType

@[expose] def GGTPTorus : Subgroup (Fin 6 → Multiplicative (ZMod 3)) where
  carrier := {x | ∏ i, x i = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Pi.mul_apply] at *
    rw [Finset.prod_mul_distrib, ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Pi.inv_apply] at *
    rw [Finset.prod_inv_distrib, ha, inv_one]

@[expose] def GGTPTorusConst : Subgroup (Fin 6 → Multiplicative (ZMod 3)) where
  carrier := {x | ∀ i j, x i = x j}
  mul_mem' := by
    intro a b ha hb i j
    simp only [Pi.mul_apply, ha i j, hb i j]
  one_mem' := by
    intro i j
    rfl
  inv_mem' := by
    intro a ha i j
    simp only [Pi.inv_apply, ha i j]

@[expose] def ggTPPermAct (σ : Equiv.Perm (Fin 6)) : GGTPTorus →* GGTPTorus where
  toFun x := ⟨fun i => x.1 (σ⁻¹ i), by
    have h : ∏ i, x.1 i = 1 := x.2
    show ∏ i, x.1 (σ⁻¹ i) = 1
    rw [Equiv.prod_comp σ⁻¹ x.1]
    exact h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end CFSG.StandardType

end
