module

public import CFSG.RankThree.PartTwo.Toolkit.M12LocalInputs

public section

namespace CFSG.RankThree.PartTwo.Toolkit.M12

open CFSG.GH74.M12.Hyp CFSG.Blueprint CFSG.RankThree.Asc83Table Subgroup
open scoped commutatorElement

theorem eq_iff_tbl {g h : G12} : g = h ↔ tbl g.1 = tbl h.1 :=
  ⟨fun e => by rw [e], fun e => Subtype.ext (tbl_injective e)⟩

theorem tblG_mul (g h : G12) : tbl (g * h).1 = tmul (tbl g.1) (tbl h.1) := tbl_mul g.1 h.1

theorem tblG_inv (g : G12) : tbl g⁻¹.1 = tinv (tbl g.1) := tbl_inv g.1

theorem tblG_pow (g : G12) (n : ℕ) : tbl (g ^ n).1 = tpow (tbl g.1) n := tbl_pow g.1 n

theorem tblG_one : tbl (1 : G12).1 = tid := tbl_one

theorem tblG_conj (g h : G12) : tbl (g * h * g⁻¹).1 = tconj (tbl g.1) (tbl h.1) := by
  rw [tblG_mul, tblG_mul, tblG_inv]
  rfl

theorem tblG_comm (g h : G12) : tbl ⁅g, h⁆.1 = tcm (tbl g.1) (tbl h.1) := by
  rw [commutatorElement_def, tblG_mul, tblG_mul, tblG_mul, tblG_inv, tblG_inv]
  rfl

@[expose] def wE (w : List Int) : G12 := ⟨wordP w, wordP_mem w⟩

theorem tbl_wE (w : List Int) : tbl (wE w).1 = wordT w := tbl_wordP w

@[expose] def x : G12 := wE wX

@[expose] def y : G12 := wE wY

theorem tbl_x : tbl x.1 = xT := tbl_wE wX

theorem tbl_y : tbl y.1 = yT := tbl_wE wY

theorem tbl_z : tbl ⁅x, y⁆.1 = zT := by rw [tblG_comm, tbl_x, tbl_y]; rfl

theorem tbl_a : tbl (x * y).1 = aT := by rw [tblG_mul, tbl_x, tbl_y]; rfl

theorem x_cube : x ^ 3 = 1 := by
  rw [eq_iff_tbl, tblG_pow, tblG_one, tbl_x]
  decide +kernel

theorem y_cube : y ^ 3 = 1 := by
  rw [eq_iff_tbl, tblG_pow, tblG_one, tbl_y]
  decide +kernel

theorem z_comm_x : Commute ⁅x, y⁆ x := by
  rw [Commute, SemiconjBy, eq_iff_tbl, tblG_mul, tblG_mul, tbl_z, tbl_x]
  decide +kernel

theorem z_comm_y : Commute ⁅x, y⁆ y := by
  rw [Commute, SemiconjBy, eq_iff_tbl, tblG_mul, tblG_mul, tbl_z, tbl_y]
  decide +kernel

theorem z_ne_one : ⁅x, y⁆ ≠ 1 := by
  rw [Ne, eq_iff_tbl, tbl_z, tblG_one]
  decide +kernel

theorem a_cube : (x * y) ^ 3 = 1 := by
  rw [eq_iff_tbl, tblG_pow, tblG_one, tbl_a]
  decide +kernel

theorem a_ne_one : x * y ≠ 1 := by
  rw [Ne, eq_iff_tbl, tbl_a, tblG_one]
  decide +kernel

@[expose] def P0 : Subgroup G12 := closure {x, y}

noncomputable abbrev basisE : E9Basis G12 := ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0

noncomputable abbrev basisF : E9Basis G12 := ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 1

noncomputable abbrev basisA : E9Basis G12 := ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 2

noncomputable abbrev basisA' : E9Basis G12 :=
  ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 3

end CFSG.RankThree.PartTwo.Toolkit.M12
