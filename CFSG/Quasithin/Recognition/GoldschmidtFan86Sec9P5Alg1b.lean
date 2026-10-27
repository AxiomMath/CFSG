module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Ids

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za : H} {y z : Fin 5 → H} {xb t w2 ub : H}
  {zm ym za' : Fin 3 → H} {e₁ e₂ : ℕ}
  (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z)

include h hR

namespace P5Ids

theorem p2_yub :
    fcomm (ym 0) ub = 1 :=
  by idc h hR

theorem p2_yza :
    ∀ i, fcomm (ym 0) (za' i) = 1 :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_uza :
    ∀ i, fcomm ub (za' i) = 1 :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_zaz :
    ∀ i j, fcomm (zm j) (za' i) = 1 :=
  by refine fin3_forall2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> idc h hR

theorem p2_zay :
    ∀ i j, fcomm (ym j) (za' i) = 1 :=
  by refine fin3_forall2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> idc h hR

theorem p2_zaw1 :
    ∀ i, fcomm w (za' i) = 1 :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_zaza :
    ∀ i j, fcomm (za' i) (za' j) = 1 :=
  by refine fin3_forall2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> idc h hR

theorem p2_prod_y :
    ym 0 * ym 1 * ym 2 = 1 :=
  by idc h hR

theorem p2_prod_za :
    za' 0 * za' 1 * za' 2 = 1 :=
  by idc h hR

theorem p2_zz_01 :
    fcomm (zm 0) (zm 1) = ub * za' 2 :=
  by idc h hR

theorem p2_zz_02 :
    fcomm (zm 0) (zm 2) = ub * za' 1 :=
  by idc h hR

theorem p2_zz_10 :
    fcomm (zm 1) (zm 0) = ub * za' 2 :=
  by idc h hR

theorem p2_zz_12 :
    fcomm (zm 1) (zm 2) = ub * za' 0 :=
  by idc h hR

theorem p2_zz_20 :
    fcomm (zm 2) (zm 0) = ub * za' 1 :=
  by idc h hR

theorem p2_zz_21 :
    fcomm (zm 2) (zm 1) = ub * za' 0 :=
  by idc h hR

theorem p2_zy_01 :
    fcomm (zm 0) (ym 1) = za' 0 :=
  by idc h hR

theorem p2_zy_02 :
    fcomm (zm 0) (ym 2) = za' 0 :=
  by idc h hR

theorem p2_zy_10 :
    fcomm (zm 1) (ym 0) = za' 1 :=
  by idc h hR

theorem p2_zy_12 :
    fcomm (zm 1) (ym 2) = za' 1 :=
  by idc h hR

theorem p2_zy_20 :
    fcomm (zm 2) (ym 0) = za' 2 :=
  by idc h hR

theorem p2_zy_21 :
    fcomm (zm 2) (ym 1) = za' 2 :=
  by idc h hR

end P5Ids

end CFSG.Quasithin.Fan86
