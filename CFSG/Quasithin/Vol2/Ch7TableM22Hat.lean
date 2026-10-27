module

public import CFSG.Quasithin.Vol2.Ch7Inputs
public import CFSG.Quasithin.Background.HM22RowMain
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_2_1_M22Hat :
    Stmt7_2_1_M22Hat := by
  intro G _ _ T L I _ hV hNM _ hrow
  have hL : Mhat22Twelve (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := hrow
  exact Mathieu.M22Row.row721M22Hat IntMod.sq_eq_one
    (autI_top_le_normalizer (T := T) (L := L) (I := I) hV hNM) hL

end CFSG.Quasithin.H13
