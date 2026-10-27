module

public import CFSG.Quasithin.EmptyFaithful.SBc16Defs
import CFSG.Quasithin.EmptyFaithful.SBc16FCoord
import CFSG.Quasithin.EmptyFaithful.SBc16FCore

public section

namespace CFSG.Quasithin

namespace SBc16

theorem noFiveD8 : NoFiveD8 := by
  intro V _ _ hV h5 V₁ V₂ h1 h2 hd A σ τ hσA hτA hσ2 hσ1 hτ1 hτ2 h16 α hαA hα5
  obtain ⟨ρ, hρ, hmat⟩ := exists_matrix_rep V hV h5 V₁ V₂ h1 h2 hd
  obtain ⟨m00, m01, m10, m11, t00, t11, t01, t10⟩ := hmat σ τ hσ2 hσ1 hτ1 hτ2
  apply h16
  have h := core_dvd (A.map ρ) (ρ σ) (ρ τ) (ρ α) (Subgroup.mem_map_of_mem ρ hσA)
    (Subgroup.mem_map_of_mem ρ hτA) (Subgroup.mem_map_of_mem ρ hαA)
    (by rw [orderOf_injective ρ hρ]; exact hα5) m00 m01 m10 m11 t00 t11 t01 t10
  rwa [Subgroup.card_map_of_injective hρ] at h

end SBc16

end CFSG.Quasithin
