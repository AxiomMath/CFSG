module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KSyl27
public import CFSG.RankThree.Native.MathieuRealThree
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Blueprint CFSG.RankThree.Native
open scoped commutatorElement

namespace KM24

def ev (w : List ℕ) : ↥NativeSporadic.M24 :=
  (w.map fun i => if i = 0 then m24T else if i = 1 then m24B else m24B⁻¹).prod

def wk1 : List ℕ := [0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0]

def wk2 : List ℕ := [0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0]

def wu : List ℕ :=
  [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2]

def x : ↥NativeSporadic.M24 := ev wk1 * m24B * (ev wk1)⁻¹

def y : ↥NativeSporadic.M24 := ev wk2 * m24B * (ev wk2)⁻¹

def u : ↥NativeSporadic.M24 := ev wu

def xP : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 12, 18] * List.formPerm [2, 14, 8] * List.formPerm [3, 16, 23] *
    List.formPerm [4, 17, 9] * List.formPerm [5, 15, 22] * List.formPerm [10, 11, 21]

def yP : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 9, 14] * List.formPerm [2, 20, 4] * List.formPerm [6, 19, 7] *
    List.formPerm [8, 13, 17] * List.formPerm [12, 15, 16] * List.formPerm [18, 23, 22]

def zP : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

def uP : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [2, 19] * List.formPerm [4, 9] * List.formPerm [5, 10] *
    List.formPerm [6, 17] * List.formPerm [8, 14] * List.formPerm [11, 15] * List.formPerm [12, 16]

set_option maxRecDepth 100000 in
theorem x_coe : ((x : ↥NativeSporadic.M24) : Equiv.Perm (Fin 24)) = xP := by decide +kernel

set_option maxRecDepth 100000 in
theorem y_coe : ((y : ↥NativeSporadic.M24) : Equiv.Perm (Fin 24)) = yP := by decide +kernel

set_option maxRecDepth 100000 in
theorem u_coe : ((u : ↥NativeSporadic.M24) : Equiv.Perm (Fin 24)) = uP := by decide +kernel

set_option maxRecDepth 100000 in
theorem z_coe : ((⁅x, y⁆ : ↥NativeSporadic.M24) : Equiv.Perm (Fin 24)) = zP := by
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, x_coe, y_coe]
  decide +kernel

theorem x_pow : x ^ 3 = 1 := by
  apply Subtype.ext
  have : xP ^ 3 = 1 := by decide +kernel
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, x_coe] using this

theorem y_pow : y ^ 3 = 1 := by
  apply Subtype.ext
  have : yP ^ 3 = 1 := by decide +kernel
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, y_coe] using this

theorem z_comm_x : ⁅x, y⁆ * x = x * ⁅x, y⁆ := by
  apply Subtype.ext
  have : zP * xP = xP * zP := by decide +kernel
  simpa only [Subgroup.coe_mul, x_coe, z_coe] using this

theorem z_comm_y : ⁅x, y⁆ * y = y * ⁅x, y⁆ := by
  apply Subtype.ext
  have : zP * yP = yP * zP := by decide +kernel
  simpa only [Subgroup.coe_mul, y_coe, z_coe] using this

theorem z_ne_one : ⁅x, y⁆ ≠ 1 := by
  intro h
  have h1 := congrArg Subtype.val h
  have : zP ≠ 1 := by decide +kernel
  exact this (by simpa only [z_coe, Subgroup.coe_one] using h1)

theorem u_sq : u * u = 1 := by
  apply Subtype.ext
  have : uP * uP = 1 := by decide +kernel
  simpa only [Subgroup.coe_mul, Subgroup.coe_one, u_coe] using this

theorem u_comm : ∀ i j k : Fin 3, u * ((x ^ (i : ℕ) * y ^ (j : ℕ) * ⁅x, y⁆ ^ (k : ℕ)) * u *
        (x ^ (i : ℕ) * y ^ (j : ℕ) * ⁅x, y⁆ ^ (k : ℕ))⁻¹) =
      ((x ^ (i : ℕ) * y ^ (j : ℕ) * ⁅x, y⁆ ^ (k : ℕ)) * u *
        (x ^ (i : ℕ) * y ^ (j : ℕ) * ⁅x, y⁆ ^ (k : ℕ))⁻¹) * u := by
  have key : ∀ i j k : Fin 3, uP * ((xP ^ (i : ℕ) * yP ^ (j : ℕ) * zP ^ (k : ℕ)) * uP *
        (xP ^ (i : ℕ) * yP ^ (j : ℕ) * zP ^ (k : ℕ))⁻¹) =
      ((xP ^ (i : ℕ) * yP ^ (j : ℕ) * zP ^ (k : ℕ)) * uP *
        (xP ^ (i : ℕ) * yP ^ (j : ℕ) * zP ^ (k : ℕ))⁻¹) * uP := by
    decide +kernel
  intro i j k
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, x_coe, y_coe, z_coe, u_coe]
    using key i j k

theorem z_move : ⁅x, y⁆ * u * ⁅x, y⁆⁻¹ ≠ u := by
  intro h
  have h1 := congrArg Subtype.val h
  have : zP * uP * zP⁻¹ ≠ uP := by decide +kernel
  exact this (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, z_coe, u_coe] using h1)

end KM24

theorem factorization_three_card_m24 :
    (Nat.card NativeSporadic.M24).factorization 3 = 3 := by
  rw [CFSG.Sporadic.Mathieu.card_M24, Nat.factorization_def _ Nat.prime_three]
  decide +kernel

theorem eInvNine_m24 : EInvNine NativeSporadic.M24 := by
  have hZ := CFSG.Sporadic.Schreier.m24_center_eq_bot'
  have hcard : Nat.card (MulAut NativeSporadic.M24) ≤ 2 * Nat.card NativeSporadic.M24 :=
    CFSG.Sporadic.Schreier.m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  exact eInvNine_of_extraspecial27 (x := KM24.x) (y := KM24.y) hZ
    (fun α hα => exists_conj_of_pow_three_of_card_le hZ hcard hα) KM24.x_pow KM24.y_pow
    KM24.z_comm_x KM24.z_comm_y KM24.z_ne_one
    factorization_three_card_m24 KM24.u_sq KM24.u_comm KM24.z_move

theorem eInvNine_of_mulEquiv_m24 {X : Type} [Group X] (e : X ≃* NativeSporadic.M24) :
    EInvNine X :=
  EInvNine.of_mulEquiv e eInvNine_m24

end CFSG.RankThree.PartTwo.Sec21.Hering214
