module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSpDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSpSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpField
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


theorem ggSecFiveBCoordBSpSpChartInput_of_frames (hfr : GGSecFiveBSpCoordFrameInput)
    (hRig : GGLabelRigidInput) : GGSecFiveBCoordBSpSpChartInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hBfull hLeta hLab hBB hnbr hG0 f K
    hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ 2 ^ f - 1 := GGSecFiveBCoordBSpSpCell.dvd_two_pow_sub_one hcell hLab hRig
  obtain ⟨s, hn⟩ : ∃ s, n = s + 3 := ⟨n - 3, by omega⟩
  subst n
  obtain ⟨hf, h5, hK𝒦, ⟨eL⟩, ⟨eK⟩, j, hji, hKeta⟩ := hcell
  have hs : 2 ≤ s := by omega
  obtain ⟨-, hBs, hxBs, -, -⟩ := hR.1.1.tableB_facts
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  have hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hNy.1.2.1
  have hKcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hNy.1.2.2.2.2.1
  have hLF := hfr G p hp hp2 (s + 1) f (by omega) hf hdvd B Bs L hR.1.1.2.1
    hR.1.2.2.1.1 ⟨eL⟩ eta i0 hLeta
  have hKF := hfr G p hp hp2 (s + 1) f (by omega) hf hdvd B Bs K hR.1.1.2.1
    (hR.1.2.2.1.2 y K hNy) ⟨eK⟩ eta j hKeta
  have hLcomp : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L := by
    obtain ⟨πL, κL, χL, hπL, hFL⟩ := hLF
    exact hR.largeEvenPComponent_L (GGSecFiveBPermSpKFrame.prime_dvd_card hp hFL)
  exact ⟨s, rfl, ggSecFiveBCoordBSpSp_charts_of_frames (s := s) hs hji hKeta hLF hKF
    (fun π κ χ hF a b hab =>
      ggSecFiveBPermSp_reflComm_K (r := s + 1) hp2 hf (by omega) hBc hBsmax hxBs hLcomp hF hab)
    (fun π κ χ hF a =>
      ggSecFiveBPermSp_singletonComm_K (r := s + 1) hp2 hf (by omega) hBc hBsmax hxBs hLcomp hF a)
    (fun π κ χ hF a b hab =>
      ggSecFiveBPermSp_reflComm_K (r := s + 1) hp2 hf (by omega) hBc hBsmax hyBs hKcomp hF hab)
    (fun π κ χ hF a =>
      ggSecFiveBPermSp_singletonComm_K (r := s + 1) hp2 hf (by omega) hBc hBsmax hyBs hKcomp hF a)⟩

end CFSG.StandardType

end
