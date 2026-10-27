module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Ids

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za : H} {y z : Fin 5 → H} {xb t w2 ub : H}
  {zm ym za' : Fin 3 → H} {e₁ e₂ : ℕ}
  (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z)

include h hR

namespace P5Ids

theorem p2_w1sq :
    w ^ 2 = zm 2 * za' 0 :=
  by idc h hR

theorem p2_zm2 :
    ∀ i, zm i ^ 2 = 1 :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_ym2 :
    ∀ i, ym i ^ 2 = 1 :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_za2 :
    ∀ i, za' i ^ 2 = 1 :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_ub2 :
    ub ^ 2 = 1 :=
  by idc h hR

theorem p2_tz :
    ∀ i, t⁻¹ * zm i * t = zm (Equiv.swap 1 2 i) :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_ty :
    ∀ i, t⁻¹ * ym i * t = ym (Equiv.swap 1 2 i) * za' (Equiv.swap 1 2 i) :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_ta :
    ∀ i, t⁻¹ * za' i * t = za' (Equiv.swap 1 2 i) :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_tub :
    t⁻¹ * ub * t = ub :=
  by idc h hR

theorem p2_w1z1 :
    fcomm w (zm 0) = ym 0 * ub * za' 0 :=
  by idc h hR

theorem p2_w1z2 :
    fcomm w (zm 1) = ym 1 :=
  by idc h hR

theorem p2_w1z3 :
    fcomm w (zm 2) = 1 :=
  by idc h hR

theorem p2_w1y1 :
    fcomm w (ym 0) = ub * za' 0 :=
  by idc h hR

theorem p2_w1y2 :
    fcomm w (ym 1) = ub * za' 0 :=
  by idc h hR

theorem p2_w1ub :
    fcomm w ub = za' 2 :=
  by idc h hR

theorem p2_zyi :
    ∀ i, fcomm (zm i) (ym i) = 1 :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

theorem p2_zub :
    ∀ i, fcomm (zm i) ub = 1 :=
  by refine fin3_forall ?_ ?_ ?_ <;> idc h hR

end P5Ids

end CFSG.Quasithin.Fan86
