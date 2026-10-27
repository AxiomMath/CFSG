module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

namespace CFSG
end CFSG
open CFSG

/-! # Normality of the centralizer setup's Fitting subgroup -/

namespace CFSG.GorensteinWalter

universe u

/-- For a centralizer setup, `F(U)` is normal in `H = C_G(t)`. -/
public theorem centralizerSetup_FU_isNormalIn_H
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : IsNormalIn c.FU c.H := by
  have hUnormalH : IsNormalIn c.U c.H := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
    · intro h hh x hx
      rcases (Subgroup.mem_map).1 hx with ⟨p, hp, rfl⟩
      have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
          pPrimeCore 2 c.H :=
        (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
          p hp (⟨h, hh⟩ : c.H)
      exact Subgroup.mem_map.mpr
        ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩
  change IsNormalIn ((fittingSubgroup c.U).map c.U.subtype) c.H
  exact map_characteristic_isNormalIn_of_isNormalIn
    (K := fittingSubgroup c.U) (hKchar := by infer_instance)
    (hHnormal := hUnormalH)

end CFSG.GorensteinWalter
