module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInf
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageOfPosition
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImage
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic

public section

namespace CFSG.StandardType

theorem ggSecFiveBReflSatInput_of_nativeImage (hPos : BOriginalPositionInput)
    (ha₀ : GGLNoncyclicInput) (hDX : GGSecFiveBCoordDExclInput) :
    GGSecFiveBReflSatInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR ι M e hP hM hx φ hφ hrefl hfix
  obtain ⟨n, e', hn5, rfl⟩ := hM
  obtain ⟨hn4, eta, i0, hK, hL⟩ :=
    hPos G p B Bs x L D J 𝒦 hR n (by omega) _
      (GGCoxeterPres.of_reindex_B (by omega) hP)
  have hφI : φ ∈ ggInduced ⊤ Bs := ggRM_ainf_le_induced hφ
  rcases hL with hLB | hLD | hLA
  · obtain ⟨c, a, ha, hca⟩ := hR.nativeImage_of_bCoordinateBlock ha₀ hn4 hLB hx hφI hfix
    exact hR.mem_ggAutomizer_of_native_bCoordinateBlock (by omega) hLB hx hφI hrefl hfix ha hca
  · exact (hDX G p B Bs x L D J 𝒦 hR n eta i0 hn4 hK hLD).elim
  · obtain ⟨c, a, ha, hca⟩ := hR.nativeImage_of_aPermutationFull ha₀ hn4 hLA hx hφI hfix
    exact hR.mem_ggAutomizer_of_native_aPermutationFull hn5 hLA hx hφI hrefl hfix ha hca

theorem ggSecFiveBFourCoordSatInput_of_nativeImage (hPos : BOriginalPositionInput)
    (ha₀ : GGLNoncyclicInput) (hDX : GGSecFiveBCoordDExclInput) :
    GGSecFiveBFourCoordSatInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR ι M e hP hM hx ht φ hφ hrefl hfix
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨e', rfl⟩ := hM
  obtain ⟨-, eta, i0, hK, hL⟩ :=
    hPos G p B Bs x L D J 𝒦 hR 4 (by norm_num) _
      (GGCoxeterPres.of_reindex_B (by norm_num) hP)
  have hφI : φ ∈ ggInduced ⊤ Bs := ggRM_ainf_le_induced hφ
  rcases hL with hLB | hLD | hLA
  · obtain ⟨c, a, ha, hca⟩ := hR.nativeImage_of_bCoordinateBlock ha₀ le_rfl hLB hx hφI hfix
    exact hR.mem_ggAutomizer_of_native_bCoordinateBlock (by norm_num) hLB hx hφI hrefl hfix ha hca
  · exact (hDX G p B Bs x L D J 𝒦 hR 4 eta i0 (by norm_num) hK hLD).elim
  · have : Fact p.Prime := ⟨hp⟩
    exact (hR.not_exists_refl_inv_of_aPermutationFull hp2 hx hK hLA ht).elim

end CFSG.StandardType

end
