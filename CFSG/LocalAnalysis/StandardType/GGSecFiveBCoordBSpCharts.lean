module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameMp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpField
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


theorem ggSecFiveBCoordBSpChartInput_of_frames (hMp : GGInnerDiagMpInput)
    (hfr : GGSecFiveBSpCoordFrameInput) (hRig : GGLabelRigidInput) :
    GGSecFiveBCoordBSpChartInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hBfull hLeta hLab hBB hnbr hG0 f K hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  have hdvd : p ∣ 2 ^ f - 1 :=
    GGSecFiveBCoordBSpCell.dvd_two_pow_sub_one hcell hLab hRig (by omega)
  obtain ⟨hf, hK𝒦, ⟨ψ, hker, hrange⟩, ⟨eL⟩, eta', -, hL', hK'⟩ := hcell
  obtain ⟨hcfg, -, hmarkAll, -, -, -⟩ := hR.1
  obtain ⟨hBle, hBs, -, hBsmax⟩ := hcfg.2.1
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  obtain ⟨-, -, hxBs, -, -⟩ := hcfg.tableB_facts
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hyBs : y ∈ Bs := hBle hNy.1.2.1
  have hKcomp : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2
      (isNeighborOf_of_ggNbr hcfg.2.2 hNy)).1
  obtain ⟨π, κ, χ', -, hκ⟩ :=
    hfr G p hp hp2 r f (by omega) hf hdvd B Bs L hcfg.2.1 hmarkAll.1 ⟨eL⟩ eta' i0 hL'
  obtain ⟨σ, χ, hσ⟩ :=
    exists_ggSecFiveBPermSpLFrame hMp hp hp2 hBs hBsmax (hmarkAll.2 y K hNy)
      (hR.card_inf_centralizer_nbr_le hBB hNy) (by omega) eta' hK' (by omega) hker hrange r π
  have hLcomp : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L :=
    hR.largeEvenPComponent_L (hκ.prime_dvd_card hp)
  exact ⟨r, rfl, σ, κ, hσ.1, hσ.2.1, hκ.1, hκ.2.1,
    ggSecFiveBPermSp_agreement_crossing_of_frames hp2 hf (by omega) hBc hBsmax
      hyBs hKcomp hxBs hLcomp hK' hσ hκ⟩

end CFSG.StandardType

end
