module

public import CFSG.Quasithin.EmptyFaithful.SzF53DichBase
public import CFSG.Quasithin.EmptyFaithful.SzF53B1Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

namespace F53B1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem B1Hyp.of_bAt (hA : F53Amalgam H M S) (h1 : bAt (γ₀ (H ⊔ M) H M) = 1)
    (hz : Zv (γ₁ (H ⊔ M) H M) ≤ centerOf (stab (γ₁ (H ⊔ M) H M)))
    (hf : ZaFacts H S (VZ S H)) : B1Hyp H M S where
  amalgam := hA
  b_one := not_Zv_γ₀_le_Qv_γ₁ hA h1
  zb_central := fun _ hx => (((zv_central_γ₁ hA).mp hz) hx).2
  zfacts := hf

end F53B1

end CFSG.Quasithin
