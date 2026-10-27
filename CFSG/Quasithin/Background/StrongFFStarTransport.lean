module

public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.D2Transport

public section

namespace CFSG.Quasithin

variable {W W' : Type*} [CommGroup W] [CommGroup W']

theorem isStrongFFStarOffender_map_congr_equiv_iff (φ : W ≃* W') {X A : Subgroup (MulAut W)} :
    IsStrongFFStarOffender (X.map (MulAut.congr φ).toMonoidHom)
        (A.map (MulAut.congr φ).toMonoidHom) ↔ IsStrongFFStarOffender X A := by
  unfold IsStrongFFStarOffender
  rw [isFFStarOffender_map_congr_equiv_iff, rAV_map_mulAutCongr]

end CFSG.Quasithin
