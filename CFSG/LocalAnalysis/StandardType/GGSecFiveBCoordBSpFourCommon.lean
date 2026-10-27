module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFourCommonDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFour
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFourOpposite
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Inputs


theorem ggSecFiveBCoordBSpFourCrossInput_of_common (hfr : GGSecFiveBSpCoordFrameInput)
    (hRig : GGLabelRigidInput) (hCh : GGSecFiveBCoordBSpFourCommonChartInput)
    (hCo : GGSecFiveBCoordBSpFourCommonCompInput) : GGSecFiveBCoordBSpFourCrossInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hBfull hLeta hLab hBB hnbr hG0 f K
    hcell j hj hKeta u v hju hjv huv hui hvi
  obtain ⟨ψ, hψ, hψJ, hψu, hψv⟩ := hCh G p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hBfull
    hLeta hLab hBB hnbr hG0 f K hcell j hj hKeta u v hju hjv huv hui hvi
  obtain ⟨d, hd, hJd⟩ := hCo G p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hBfull
    hLeta hLab hBB hnbr hG0 f K hcell j hj hKeta u v hju hjv huv hui hvi
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ 2 ^ f - 1 := hcell.dvd_two_pow_sub_one hLab hRig
  obtain ⟨hf, hn4, -, ⟨eL⟩, -⟩ := hcell
  subst hn4
  obtain ⟨-, hBs, hxBs, -, -⟩ := hR.1.1.tableB_facts
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  have hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  obtain ⟨πL, κL, χL, hπL, hFL⟩ := hfr G p hp hp2 2 f le_rfl hf hdvd B Bs L hR.1.1.2.1
    hR.1.2.2.1.1 ⟨eL⟩ eta i0 hLeta
  have hLcomp : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L :=
    hR.largeEvenPComponent_L (GGSecFiveBPermSpKFrame.prime_dvd_card hp hFL)
  exact SpFourOpposite.ggSecFiveBCoordBSpFour_cross_of_isComponentOf hf hj hju hjv huv hui hvi
    hBc hLeta hKeta πL κL hπL
    (fun a b hab =>
      ggSecFiveBPermSp_reflComm_K (r := 2) hp2 hf le_rfl hBc hBsmax hxBs hLcomp hFL hab)
    (fun a => ggSecFiveBPermSp_singletonComm_K (r := 2) hp2 hf le_rfl hBc hBsmax hxBs hLcomp hFL a)
    rfl ψ hψ hψJ hψu hψv hd hJd

end Inputs

end CFSG.StandardType

end
