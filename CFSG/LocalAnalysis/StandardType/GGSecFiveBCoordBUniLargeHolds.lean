module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniLeaves
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniFrames
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOm
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

theorem ggSecFiveBCoordBUniLargeInput_holds :
    GGSecFiveBCoordBUniLargeInput := by
  intro hMp hRig G _ _ p B Bs x L D J 𝒦 hR _ n _ _ h5n _ _ _ _ _ hBB _ _ f K hcell
  have hf : 2 ≤ f := hcell.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmo : Odd m := by
    obtain ⟨j, hj⟩ := hcell.2.1
    exact ⟨j - 1, by omega⟩
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨eta', hAK, hxBs, hLc, F, _, _, _, _, E, hUF, π, -, ⟨κ, χ, hκ⟩, σ, χ', hσ⟩ :=
    hcell.exists_frames hMp hRig hR hBB (by omega)
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have hJL : (σ.comp (uniCast hUF m)).range ≤ L :=
    hσ.range_comp_uniCast_le hUF hf hp (by omega) fun c d hcd hc hd =>
      hκ.ggBlockComm_le hBsC hxBs hLc (by omega) hcd hc hd
  obtain ⟨Ψ, hΨ, hΨr⟩ := ggSecFiveBPermUniOm_of_frames hp2
    hcell.2.2.1 (by omega) hUF hBsC hxBs hLc hAK hσ hκ hJL
  obtain ⟨ψ, hψ, hψr⟩ := exists_ggU_POmegaPlus_of_injective_normOmega (by omega) hmo hΨ
  exact ⟨ψ, hψ, by rw [hψr, hΨr, sup_comm]⟩

end CFSG.StandardType

end
