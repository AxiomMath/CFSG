module

public import CFSG.Quasithin.Background.FixVLatticeSup

public section

namespace CFSG.Quasithin.FixVLat

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem isElemAbelian2_map_iff_of_injective {φ : MulAut V →* MulAut W}
    (hφ : Function.Injective φ) {A : Subgroup (MulAut V)} :
    IsElemAbelian2 (A.map φ) ↔ IsElemAbelian2 A := by
  rw [isElemAbelian2_map_iff hφ]
  simp only [IsElemAbelian2, pow_two]

theorem isElemAbelian2_map_congr_iff (e : V ≃* W) {A : Subgroup (MulAut V)} :
    IsElemAbelian2 (A.map (MulAut.congr e).toMonoidHom) ↔ IsElemAbelian2 A :=
  isElemAbelian2_map_iff_of_injective (MulAut.congr e).injective

end CFSG.Quasithin.FixVLat
