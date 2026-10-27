module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Fin
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.Quasithin.H13.L32A.C.Alt6

open Equiv Equiv.Perm
section DecideBounded

open scoped CFSG.Decide.Bounded

@[expose] def z6 : Perm (Fin 6) := swap 0 1 * swap 2 3

@[expose] def a6 : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def b6 : Perm (Fin 6) := swap 0 1 * swap 4 5

@[expose] def d6 : Perm (Fin 6) := swap 0 3 * swap 0 1 * swap 0 2 * swap 4 5

@[expose] def x0 : Perm (Fin 6) := swap 0 2 * swap 0 1

@[expose] def y0 : Perm (Fin 6) := swap 0 4 * swap 0 2 * (swap 1 5 * swap 1 3)

@[expose] def d0List : List (Perm (Fin 6)) :=
  [1, z6, a6, z6 * a6, b6, z6 * b6, d6, d6 * z6]

@[expose] def e1List : List (Perm (Fin 6)) := [1, z6, a6, z6 * a6]

@[expose] def e2List : List (Perm (Fin 6)) := [1, z6, b6, z6 * b6]

theorem d0_sign : ∀ g ∈ d0List, sign g = 1 := by
  decide +kernel

theorem d0_mul : ∀ g ∈ d0List, ∀ h ∈ d0List, g * h ∈ d0List := by
  decide +kernel

theorem d0_inv : ∀ g ∈ d0List, g⁻¹ ∈ d0List := by
  decide +kernel

theorem d0_nodup : d0List.Nodup := by
  decide +kernel

theorem e1_sub : ∀ g ∈ e1List, g ∈ d0List := by
  decide +kernel

theorem e2_sub : ∀ g ∈ e2List, g ∈ d0List := by
  decide +kernel

theorem e1_mul : ∀ g ∈ e1List, ∀ h ∈ e1List, g * h ∈ e1List := by
  decide +kernel

theorem e2_mul : ∀ g ∈ e2List, ∀ h ∈ e2List, g * h ∈ e2List := by
  decide +kernel

@[expose] def invList : List (Perm (Fin 6)) := [z6, a6, z6 * a6, b6, z6 * b6]

theorem inv_D0 : ∀ u ∈ d0List, u ≠ 1 → u * u = 1 → u ∈ invList := by
  decide +kernel

theorem klein_D0 : ∀ u ∈ invList, ∀ v ∈ invList, u ≠ v → u * v = v * u →
    u ∈ e1List ∧ v ∈ e1List ∨ u ∈ e2List ∧ v ∈ e2List := by
  decide +kernel

theorem fixed_of_normalizes_E1 : ∀ y : Perm (Fin 6), y ^ 3 = 1 → y ≠ 1 →
    (∀ e ∈ e1List, y * e * y⁻¹ ∈ e1List) → ∃ i, y i = i := by
  decide +kernel

theorem fpf_of_normalizes_E2 : ∀ y : Perm (Fin 6), y ^ 3 = 1 → y ≠ 1 →
    (∀ e ∈ e2List, y * e * y⁻¹ ∈ e2List) → ∀ i, y i ≠ i := by
  decide +kernel

theorem x0_y0_facts : sign x0 = 1 ∧ x0 ^ 3 = 1 ∧ x0 ≠ 1 ∧ x0 3 = 3 ∧
    (∀ e ∈ e1List, x0 * e * x0⁻¹ ∈ e1List) ∧ sign y0 = 1 ∧ y0 ^ 3 = 1 ∧ y0 ≠ 1 ∧
    (∀ i, y0 i ≠ i) ∧ (∀ e ∈ e2List, y0 * e * y0⁻¹ ∈ e2List) ∧
    ¬ (∀ e ∈ e1List, y0 * e * y0⁻¹ ∈ e1List) := by
  decide +kernel

theorem one_mem_lists : (1 : Perm (Fin 6)) ∈ d0List ∧ (1 : Perm (Fin 6)) ∈ e1List ∧
    (1 : Perm (Fin 6)) ∈ e2List := by
  decide +kernel

theorem e1_inv : ∀ g ∈ e1List, g⁻¹ ∈ e1List := by
  decide +kernel

theorem e2_inv : ∀ g ∈ e2List, g⁻¹ ∈ e2List := by
  decide +kernel

theorem d0_normalizes_e1 : ∀ d ∈ d0List, ∀ e ∈ e1List, d * e * d⁻¹ ∈ e1List := by
  decide +kernel

theorem d0_normalizes_e2 : ∀ d ∈ d0List, ∀ e ∈ e2List, d * e * d⁻¹ ∈ e2List := by
  decide +kernel

theorem zab_facts : z6 * z6 = 1 ∧ a6 * a6 = 1 ∧ b6 * b6 = 1 ∧ z6 ≠ 1 ∧ a6 ≠ 1 ∧ b6 ≠ 1 ∧
    z6 ≠ a6 ∧ z6 ≠ b6 ∧ z6 * a6 = a6 * z6 ∧ z6 * b6 = b6 * z6 := by
  decide +kernel

theorem e_nodup : e1List.Nodup ∧ e2List.Nodup := by
  decide +kernel

end DecideBounded

theorem n1_count : (Finset.univ.filter fun g : Perm (Fin 6) =>
    sign g = 1 ∧ ∀ e ∈ e1List, g * e * g⁻¹ ∈ e1List).card = 24 := by
  open scoped CFSG.Decide.Bounded in
  rw [Finset.filter_congr_decidable]
  decide +kernel

theorem n2_count : (Finset.univ.filter fun g : Perm (Fin 6) =>
    sign g = 1 ∧ ∀ e ∈ e2List, g * e * g⁻¹ ∈ e2List).card = 24 := by
  open scoped CFSG.Decide.Bounded in
  rw [Finset.filter_congr_decidable]
  decide +kernel

theorem x0y0_order_five : (x0 * y0) ^ 5 = 1 ∧ x0 * y0 ≠ 1 := by
  decide +kernel

end CFSG.Quasithin.H13.L32A.C.Alt6
