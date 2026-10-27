module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.Quasithin.S15223.F7

open Equiv Equiv.Perm

@[expose] def c1 : Perm (Fin 7) := swap 0 1 * swap 1 2

@[expose] def c2 : Perm (Fin 7) := swap 3 4 * swap 4 5

@[expose] def y0L : List (Perm (Fin 7)) :=
  [1, c1, c1 * c1, c2, c1 * c2, c1 * c1 * c2, c2 * c2, c1 * c2 * c2, c1 * c1 * c2 * c2]

theorem chk_y0L_mul : (y0L.all fun a => y0L.all fun b => y0L.contains (a * b)) = true := by
  decide +kernel

theorem chk_y0L_inv : (y0L.all fun a => y0L.contains a⁻¹) = true := by decide +kernel

theorem mul_mem_y0L : ∀ a ∈ y0L, ∀ b ∈ y0L, a * b ∈ y0L := fun a ha b hb =>
  List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp chk_y0L_mul a ha) b hb)

theorem inv_mem_y0L : ∀ a ∈ y0L, a⁻¹ ∈ y0L := fun a ha =>
  List.contains_iff_mem.mp (List.all_eq_true.mp chk_y0L_inv a ha)

@[expose] def y0 : Subgroup (Perm (Fin 7)) where
  carrier := {σ | σ ∈ y0L}
  one_mem' := by decide +kernel
  mul_mem' {a b} ha hb := mul_mem_y0L a ha b hb
  inv_mem' {a} ha := inv_mem_y0L a ha

theorem mem_y0 {σ : Perm (Fin 7)} : σ ∈ y0 ↔ σ ∈ y0L := Iff.rfl

theorem y0L_card : y0L.toFinset.card = 9 := by decide +kernel

theorem card_y0 : Nat.card y0 = 9 := by
  have h : (y0 : Set (Perm (Fin 7))) = ↑y0L.toFinset := by
    ext σ
    simp [mem_y0]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset, y0L_card]

theorem isPGroup_y0 : IsPGroup 3 y0 := IsPGroup.of_card (n := 2) (by rw [card_y0]; norm_num)

theorem not_dvd_index {P : Subgroup (Perm (Fin 7))} (hP : Nat.card P = 9) : ¬ 3 ∣ P.index := by
  intro h
  have e := Subgroup.card_mul_index P
  rw [hP, Nat.card_perm, Nat.card_fin] at e
  have h7 : Nat.factorial 7 = 5040 := by decide
  rw [h7] at e
  omega

theorem exists_order_three : ∀ a b : Fin 7, a ≠ b → ∃ y ∈ y0L,
    (swap a b * (y * swap a b * y⁻¹)) ^ 3 = 1 ∧ swap a b * (y * swap a b * y⁻¹) ≠ 1 := by
  decide +kernel

end CFSG.Quasithin.S15223.F7
