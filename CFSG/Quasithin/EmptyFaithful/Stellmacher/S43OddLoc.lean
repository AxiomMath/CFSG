module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom Equiv Mod6

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem le_Zv_of_normalized (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ) {K : Subgroup G} (hK : K ≤ Vn δ)
    (hN : stab ρ ≤ Subgroup.normalizer ((K ⊔ Zv ρ : Subgroup G) : Set G)) : K ≤ Zv ρ := by
  have hs' : Sit43 ρ := hs.of_vtype_false hρ
  have hZV : Zv ρ ≤ Vn δ := Sit43.Zv_le_Vn hδ
  have := hs'.S13 hA h26 hδ hN le_sup_right (sup_le hK hZV)
  exact le_sup_left.trans this.le

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
