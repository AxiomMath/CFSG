module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

namespace CFSG
end CFSG
open CFSG

/-! # Normality of the odd core in a centralizer setup -/

namespace CFSG.GorensteinWalter

universe u

/-- In a centralizer setup, `U = O(H)` is normal in `H`. -/
public theorem centralizerSetup_U_isNormalIn_H
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : IsNormalIn c.U c.H := by
  refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 c.H), ?_⟩
  intro h hh x hx
  rcases (Subgroup.mem_map).1 hx with ⟨p, hp, rfl⟩
  have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
      pPrimeCore 2 c.H :=
    (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem p hp ⟨h, hh⟩
  exact Subgroup.mem_map.mpr
    ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩

end CFSG.GorensteinWalter
