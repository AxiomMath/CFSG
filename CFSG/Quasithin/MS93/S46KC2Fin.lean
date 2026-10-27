module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.Quasithin.MS93.S46.KC2

open scoped Matrix

@[expose] def cr (u v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

@[expose] def lv : Fin 6 → Fin 3 → ZMod 2 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1]]

@[expose] def tab (i j : Fin 6) : Fin 3 → ZMod 2 := cr (lv i) (lv j)

@[expose] def bsum (c : Fin 6 → Bool) (L : List (Fin 6)) (j : Fin 6) : Fin 3 → ZMod 2 :=
  (L.map fun i => if c i then tab i j else 0).sum

@[expose] def qsum (c : Fin 6 → Bool) : List (Fin 6) → Fin 3 → ZMod 2
  | [] => 0
  | i :: L => (if c i then bsum c L i else 0) + qsum c L

theorem bsum_nil (c : Fin 6 → Bool) (j : Fin 6) : bsum c [] j = 0 := rfl

theorem bsum_cons (c : Fin 6 → Bool) (i : Fin 6) (L : List (Fin 6)) (j : Fin 6) :
    bsum c (i :: L) j = (if c i then tab i j else 0) + bsum c L j := by
  simp [bsum]

theorem qsum_nil (c : Fin 6 → Bool) : qsum c [] = 0 := rfl

theorem qsum_cons (c : Fin 6 → Bool) (i : Fin 6) (L : List (Fin 6)) :
    qsum c (i :: L) = (if c i then bsum c L i else 0) + qsum c L := rfl

@[expose] def pencil : Fin 6 → Bool := ![true, true, false, true, false, false]

theorem qsum_pencil : qsum pencil (List.finRange 6) ≠ 0 := by
  decide

theorem tab_self : ∀ i, tab i i = 0 := by
  decide

theorem lv_ne_zero : ∀ i, lv i ≠ 0 := by
  decide

private theorem lv_inj : ∀ i j, lv i = lv j → i = j := by
  decide

theorem lv_injective : Function.Injective lv := fun i j h => lv_inj i j h

@[expose] def third (l m : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  if cr l m 0 ≠ 0 then ![1, 0, 0] else if cr l m 1 ≠ 0 then ![0, 1, 0] else ![0, 0, 1]

@[expose] def matN (l m : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of ![l, m, third l m]

private theorem det_matN_aux : ∀ l m : Fin 3 → ZMod 2, l ≠ 0 → m ≠ 0 → l ≠ m →
    matN l m 0 0 * matN l m 1 1 * matN l m 2 2 - matN l m 0 0 * matN l m 1 2 * matN l m 2 1 -
      matN l m 0 1 * matN l m 1 0 * matN l m 2 2 + matN l m 0 1 * matN l m 1 2 * matN l m 2 0 +
      matN l m 0 2 * matN l m 1 0 * matN l m 2 1 - matN l m 0 2 * matN l m 1 1 * matN l m 2 0 =
      1 := by
  decide

theorem det_matN {l m : Fin 3 → ZMod 2} (hl : l ≠ 0) (hm : m ≠ 0) (hlm : l ≠ m) :
    (matN l m).det = 1 := by
  rw [Matrix.det_fin_three]
  exact det_matN_aux l m hl hm hlm

end CFSG.Quasithin.MS93.S46.KC2
