module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Ids

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H} {xb t ub : H}
  {zm ym za' : Fin 3 → H}

namespace IdsBase

variable (h : IdsBase w za y z xb t ub zm ym za')

include h

theorem wy_zero (hR : P1Rel x w za y z) : w⁻¹ * ym 0 * w = ym 0 * ub * za' 0 := by
  simp only [h.ym0, h.ub_eq, h.za0]
  coll hR

theorem cy_zero (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    c⁻¹ * ym 0 * c = ym 0 := by
  simp only [h.ym0]
  collc0 hR hC

theorem cy_one (hR : P1Rel x w za y z) (hC : P1cRel x za c y z)
    (h2 : c⁻¹ * ym 2 * c = ym 2 * za' 2) : c⁻¹ * ym 1 * c = ym 1 * za' 2 := by
  have h0 := h.cy_zero hR hC
  rw [h.ym1]
  calc c⁻¹ * (ym 0 * ym 2) * c = (c⁻¹ * ym 0 * c) * (c⁻¹ * ym 2 * c) := by group
    _ = ym 0 * ym 2 * za' 2 := by rw [h0, h2]; group

end IdsBase

namespace E1Ids

variable (h : E1Ids w za y z xb t ub zm ym za')

include h

theorem wy_two (hR : P1Rel x w za y z) : w⁻¹ * ym 2 * w = ym 2 := by
  idc h hR

theorem cy_two (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    c⁻¹ * ym 2 * c = ym 2 * za' 2 := by
  idc0 h hR hC

end E1Ids

namespace E0Ids

variable (h : E0Ids w za y z xb t ub zm ym za')

include h

theorem wy_two (hR : P1Rel x w za y z) : w⁻¹ * ym 2 * w = ym 2 * za' 2 := by
  idc h hR

theorem cy_two (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    c⁻¹ * ym 2 * c = ym 2 * za' 2 := by
  idc0 h hR hC

end E0Ids

end CFSG.Quasithin.Fan86
