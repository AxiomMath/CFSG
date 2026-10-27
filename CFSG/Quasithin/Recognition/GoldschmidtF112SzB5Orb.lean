module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F7Geometry

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open scoped Pointwise

namespace F112SzB5

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G} {z : G}

section Orbit

variable {G₀ G₁ G₂ : Subgroup G}

omit [Finite G] in
theorem ncard_orbit_comap {E : Subgroup G} (hE : E ≤ G₀) (v : CosetGeom G₀ G₁ G₂) :
    (MulAction.orbit ↥(E.comap G₀.subtype) v).ncard = (stab v).relIndex E := by
  have h1 : (E.comap G₀.subtype).map G₀.subtype = E :=
    Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
  rw [← MulAction.index_stabilizer, ← MulAction.stabilizer_subgroupOf, ← Subgroup.relIndex,
    ← Subgroup.relIndex_map_map_of_injective (f := G₀.subtype) _ _ G₀.subtype_injective, h1]
  rfl

end Orbit

end F112SzB5

end CFSG.Quasithin
