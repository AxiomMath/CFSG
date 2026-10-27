module

public import CFSG.Quasithin.Background.FixVTransport

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem fixV_zpowers_conj (g y : MulAut V) :
    fixV (Subgroup.zpowers (g * y * g⁻¹)) = (fixV (Subgroup.zpowers y)).map g.toMonoidHom := by
  rw [← fixV_map_conj_eq, MonoidHom.map_zpowers]
  rfl

theorem card_fixV_zpowers_conj (g y : MulAut V) :
    Nat.card (fixV (Subgroup.zpowers (g * y * g⁻¹))) = Nat.card (fixV (Subgroup.zpowers y)) := by
  rw [fixV_zpowers_conj, Subgroup.card_map_of_injective g.injective]

end CFSG.Quasithin
