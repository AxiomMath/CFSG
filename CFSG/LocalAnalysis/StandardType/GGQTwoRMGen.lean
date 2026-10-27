module

public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFront
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameL
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMOut
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMult
public import CFSG.LocalAnalysis.StandardType.GGQTwoDeg
public import CFSG.LocalAnalysis.StandardType.GGQTwoDegCartanHolds
public import CFSG.LocalAnalysis.StandardType.GGQTwoRMGlue
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlob
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrAsm

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan

theorem qTwoRMGen_holds
    (hEn : GGSecFiveNSEnnolaInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hTCJ : GGTCJKnown) (hZS : ZS.UseInput) : QTwoRMGenProducer := by
  intro G _ _ p B Bs x L D J 𝒦 hG
  obtain ⟨hp, m, hm, hL⟩ := qTwo_front hG hEn
  subst hp
  have hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hG.1
  obtain ⟨F, hFm⟩ := qTwo_frameL hcfg hm hL
  have hGI : GGThmIHyp 3 B x L := hcfg.1.1.1
  have hBs : GGBstar 3 B Bs := hcfg.1.1.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := F.hBsN
  have hGen := qTwo_gen2 hG hm hL hEn F hFm hLB hPJ hTCJ
  obtain ⟨k, d, c, hrow, hmodel⟩ := qTwo_localRowOut hGI hBs hN hm hL
    (fun h3 => qTwo_psuTrivialMultiplier hm h3) hcfg F hFm
  obtain ⟨ι, M, e, hpres, ⟨n, e', hn5, hM⟩, r, hr, hrc, h6⟩ := hG.2.2.2
  have hwin := qTwo_proper_model_of_row hcfg hrow hm hpres (N := n + 1) (by omega) hM ggCartanRankLe_holds hGen
  have hLM : QTwoLocalModel m Bs L x := hmodel hwin.2
  have hA : GGWeylOfType 3 (CoxeterMatrix.A (n + 1 - 1)) (ggAutomizerJoin L Bs 𝒦) := by
    have h0 : GGWeylOfType 3 M (ggAutomizerJoin L Bs 𝒦) := ⟨e, hpres.2⟩
    rw [hM] at h0
    exact GGWeylOfType.of_reindex h0
  have hN1 : m + 1 ≤ n + 1 := by rcases hwin.1 with h | ⟨h, -⟩ <;> omega
  have hN2 : n + 1 ≤ m + 2 := by rcases hwin.1 with h | ⟨h, -⟩ <;> omega
  exact ⟨qTwo_rm2 hcfg hm hLM (fun hC => qTwo_ainf_weyl hZS hcfg hm hN1 hN2 hA hLM hC), hGen⟩

end CFSG.StandardType.QTwo

end
