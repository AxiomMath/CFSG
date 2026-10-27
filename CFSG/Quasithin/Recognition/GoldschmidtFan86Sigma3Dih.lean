module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open DihedralGroup
open scoped commutatorElement

abbrev a0 : DihedralGroup 4 := r 2

@[expose] def inA (x : DihedralGroup 4) : Prop := x = r 0 ∨ x = r 2 ∨ x = sr 0 ∨ x = sr 2

@[expose] def inB (x : DihedralGroup 4) : Prop := x = r 0 ∨ x = r 2 ∨ x = sr 1 ∨ x = sr 3

instance : DecidablePred inA := fun x => by unfold inA; infer_instance
instance : DecidablePred inB := fun x => by unfold inB; infer_instance

@[expose] def kleinA : Subgroup (DihedralGroup 4) where
  carrier := {x | inA x}
  mul_mem' := by
    have : ∀ a b : DihedralGroup 4, inA a → inA b → inA (a * b) := by decide
    exact fun {a b} ha hb => this a b ha hb
  one_mem' := by decide
  inv_mem' := by
    have : ∀ a : DihedralGroup 4, inA a → inA a⁻¹ := by decide
    exact fun {a} ha => this a ha

@[expose] def kleinB : Subgroup (DihedralGroup 4) where
  carrier := {x | inB x}
  mul_mem' := by
    have : ∀ a b : DihedralGroup 4, inB a → inB b → inB (a * b) := by decide
    exact fun {a b} ha hb => this a b ha hb
  one_mem' := by decide
  inv_mem' := by
    have : ∀ a : DihedralGroup 4, inB a → inB a⁻¹ := by decide
    exact fun {a} ha => this a ha

theorem mem_kleinA {x : DihedralGroup 4} : x ∈ kleinA ↔ inA x := Iff.rfl

theorem mem_kleinB {x : DihedralGroup 4} : x ∈ kleinB ↔ inB x := Iff.rfl

theorem comm_mem (x y : DihedralGroup 4) : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = a0 := by
  revert x y; decide

theorem central_iff (x : DihedralGroup 4) :
    (∀ y, x * y = y * x) ↔ x = r 0 ∨ x = r 2 := by
  revert x; decide

theorem exists_comm (x : DihedralGroup 4) (hx : ¬ (x = r 0 ∨ x = r 2)) : ∃ y, ⁅x, y⁆ = a0 := by
  revert x; decide

theorem cent_cases (x : DihedralGroup 4) (hx2 : x * x = 1) (hx : ¬ (x = r 0 ∨ x = r 2)) :
    (∀ y, x * y = y * x ↔ inA y) ∨ (∀ y, x * y = y * x ↔ inB y) := by
  revert x; decide

theorem cent_A (x : DihedralGroup 4) (hx : inA x) (hx' : ¬ (x = r 0 ∨ x = r 2)) :
    ∀ y, x * y = y * x ↔ inA y := by
  revert x; decide

theorem cent_B (x : DihedralGroup 4) (hx : inB x) (hx' : ¬ (x = r 0 ∨ x = r 2)) :
    ∀ y, x * y = y * x ↔ inB y := by
  revert x; decide

theorem normal_inA (g x : DihedralGroup 4) (hx : inA x) : inA (g * x * g⁻¹) := by
  revert g x; decide

theorem normal_inB (g x : DihedralGroup 4) (hx : inB x) : inB (g * x * g⁻¹) := by
  revert g x; decide

end CFSG.Quasithin.Fan86.Sigma3
