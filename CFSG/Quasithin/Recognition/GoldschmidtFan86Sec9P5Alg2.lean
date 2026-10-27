module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Ids

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H} {xb t w2 ub : H}
  {zm ym za' : Fin 3 → H} {e₁ e₂ : ℕ}
  (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z)
  (hC : P1cRel x za c y z)

include h hR hC

namespace P5Ids

theorem p2c_cz2 (_hwc : fcomm w c = 1) : fcomm c (zm 1) = ub * za' 2 := by idcc h hR hC _hwc

theorem p2c_cz1 (_hwc : fcomm w c = 1) : fcomm c (zm 0) = 1 := by idcc h hR hC _hwc

theorem p2c_cz3 (_hwc : fcomm w c = 1) : fcomm c (zm 2) = 1 := by idcc h hR hC _hwc

theorem p2c_cy1 (_hwc : fcomm w c = 1) : fcomm c (ym 0) = 1 := by idcc h hR hC _hwc

theorem p2c_cub (_hwc : fcomm w c = 1) : fcomm c ub = 1 := by idcc h hR hC _hwc

theorem p2c_cy2 (_hwc : fcomm w c = 1) : fcomm c (ym 1) = za' 2 := by idcc h hR hC _hwc

theorem p2c_cy3 (_hwc : fcomm w c = 1) : fcomm c (ym 2) = za' 2 := by idcc h hR hC _hwc

theorem p2c_cza (_hwc : fcomm w c = 1) : ∀ i, fcomm c (za' i) = 1 := by
  refine fin3_forall ?_ ?_ ?_ <;> idcc h hR hC _hwc

theorem p2cRel912 (hwc : fcomm w c = 1) : P2cRel912 ub c zm ym za' where
  c2 := by rw [h.za0]; exact hC.c2
  cz2 := h.p2c_cz2 hR hC hwc
  cz1 := h.p2c_cz1 hR hC hwc
  cz3 := h.p2c_cz3 hR hC hwc
  cy1 := h.p2c_cy1 hR hC hwc
  cub := h.p2c_cub hR hC hwc
  cy2 := h.p2c_cy2 hR hC hwc
  cy3 := h.p2c_cy3 hR hC hwc
  cza := h.p2c_cza hR hC hwc

end P5Ids

end CFSG.Quasithin.Fan86
