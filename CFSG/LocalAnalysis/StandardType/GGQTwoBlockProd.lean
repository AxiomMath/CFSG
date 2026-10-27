module

public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoRMGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartBlocks
public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsm
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixFarAsm
public import CFSG.LocalAnalysis.StandardType.GGQTwoU5Row
public import CFSG.LocalAnalysis.StandardType.GGQTwoDegFrame
public import Certificates.Certificate1649001

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan
  CFSG.StandardType.QTwo.SixPoint


theorem qTwoBlock_holds
    (hEn : GGSecFiveNSEnnolaInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hTCJ : GGTCJKnown) (hZS : ZS.UseInput) (hQ2 : GGSecFiveQ2PrimeLInput) (K : Type) [Field K] [Finite K] [CharP K 2] :
    QTwoBlockProducer K := by
  intro hK G _ _ p B Bs x L D J 𝒦 hcfg hT1 hSL ι M e hpres n e' hn5 hM hr6
  have hG : QTwoJoinGuard p B Bs x L D J 𝒦 := ⟨hcfg, hT1, hSL, ι, M, e, hpres, ⟨n, e', hn5, hM⟩, hr6⟩
  obtain ⟨hp, m, hm, hL⟩ := qTwo_front hG hEn
  subst hp
  obtain ⟨F, hFm⟩ := qTwo_frameL hcfg hm hL
  have hGI : GGThmIHyp 3 B x L := hcfg.1.1.1
  have hBs : GGBstar 3 B Bs := hcfg.1.1.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := F.hBsN
  have hRMGen : QTwoRMGenAt 3 B Bs x L D J 𝒦 := qTwoRMGen_holds hEn hLB hPJ hTCJ hZS G 3 B Bs x L D J 𝒦 hG
  obtain ⟨k, d, c, hrow, hmodel⟩ := qTwo_localRowOut hGI hBs hN hm hL
    (fun h3 => qTwo_psuTrivialMultiplier hm h3) hcfg F hFm
  have hwin := qTwo_proper_model_of_row hcfg hrow hm hpres (N := n + 1) (by omega) hM
    ggCartanRankLe_holds hRMGen.hGen
  have hLM : QTwoLocalModel m Bs L x := hmodel hwin.2
  have hN' : n = m ∨ (n = m + 1 ∧ 3 ∣ n + 1) := by
    rcases hwin.1 with h | ⟨h, h3⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, h3⟩
  obtain ⟨ρA, hrefl, -⟩ := qTwoDegFrame_perm_equiv (A := ggAutomizerJoin L Bs 𝒦) (e := e)
    hpres.2 (N := n + 1) (by omega) (e' := e') hM
  let S : QTwoChartSetting B Bs x L D J 𝒦 m n := ⟨hcfg, hm, hN', hLM, hRMGen, ρA, hrefl⟩
  have hodd6 : m = 6 → Odd (Nat.card (Subgroup.center ↥L)) := by
    rintro rfl
    have hk3 : (k = QTwoRowKind.prime ∨ k = QTwoRowKind.suFull) := hwin.2
    have hd : d = 6 := by
      rcases hk3 with rfl | rfl
      · exact (hrow.dc.1 rfl).1
      · exact (hrow.dc.2.1 rfl).1
    have hn6 : n = 6 := by omega
    subst hn6
    exact qTwoDeg_odd_center_of_q2PrimeL hQ2 hcfg hrow hd hpres (e' := e') hM hL
  obtain ⟨Bk⟩ := qTwo_canonBlocks S F hFm hodd6 hK
  refine qTwo_weakPhanSystem_of_blocks hK hm hN' Bk ?_
  intro hm5 a b c' d' e'' f' ha hb hc hd he hf x' hx y hy
  subst hm5
  have hn : n = 5 := by omega
  subst hn
  have hk : k = QTwoRowKind.prime := by
    by_contra hne
    have := hrow.dvd hne
    omega
  have h5 : Nat.card Bs = 3 ^ 5 := by
    have h := hrow.card
    rwa [(hrow.dc.1 hk).1] at h
  have hodd := qTwo_oddCenter_QTwoH hcfg hL h5
  have ha' : a = 0 := Fin.ext (by simpa using ha)
  have hb' : b = 1 := Fin.ext (by simpa using hb)
  have hc' : c' = 2 := Fin.ext (by simpa using hc)
  have hd' : d' = 3 := Fin.ext (by simpa using hd)
  have he' : e'' = 4 := Fin.ext (by simpa using he)
  have hf' : f' = 5 := Fin.ext (by simpa using hf)
  subst ha' hb' hc' hd' he' hf'
  exact qTwoSix_far hK Bk hodd x' hx y hy

end CFSG.StandardType.QTwo

end
