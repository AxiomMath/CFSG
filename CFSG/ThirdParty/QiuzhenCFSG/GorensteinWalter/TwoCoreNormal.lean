module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-! # Ambient normality of the two-core -/

namespace CFSG.GorensteinWalter

universe u

/-- The ambient image of the internal `2`-core of a subgroup is normal in
that subgroup. -/
public theorem twoCoreOf_isNormalIn
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    IsNormalIn (twoCoreOf H) H := by
  refine ⟨?_, ?_⟩
  · exact Subgroup.map_subtype_le (pCore 2 H)
  · intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : H) * x0 * (⟨h, hh⟩ : H)⁻¹,
        (pCore_normal (p := 2) (G := H)).conj_mem
          x0 hx0 (⟨h, hh⟩ : H), rfl⟩

end CFSG.GorensteinWalter
