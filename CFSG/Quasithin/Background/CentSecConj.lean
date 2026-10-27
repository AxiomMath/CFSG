module

public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

namespace StabLat

variable {V : Type*} [CommGroup V]

theorem conj_mem_centSec {W U : Subgroup V} {h g : MulAut V} (hhW : h ∈ stabSub W)
    (hhU : h ∈ stabSub U) (hg : g ∈ centSec W U) : h * g * h⁻¹ ∈ centSec W U := by
  refine ⟨(stabSub W).mul_mem ((stabSub W).mul_mem hhW hg.1) ((stabSub W).inv_mem hhW),
    fun w hw => ?_⟩
  have hw' : h⁻¹ w ∈ W := ((stabSub W).inv_mem hhW w).2 hw
  have h1 := hg.2 (h⁻¹ w) hw'
  have h2 : h (g (h⁻¹ w) * (h⁻¹ w)⁻¹) ∈ U := (hhU _).2 h1
  have h3 : h (g (h⁻¹ w) * (h⁻¹ w)⁻¹) = (h * g * h⁻¹) w * w⁻¹ := by
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.apply_inv_self]
  rwa [h3] at h2

end StabLat

end CFSG.Quasithin
