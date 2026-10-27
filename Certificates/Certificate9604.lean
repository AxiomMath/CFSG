module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaHNRankData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaMc.HN
import CFSG.Certificates.Kernel.OpsMcertNSound

public section

set_option maxRecDepth 400000

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.Blueprint CertificateChecks.KernelGLQ.HNTwo

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaHNRank
  CFSG.Blueprint.NativeSporadic in
theorem certificate9604 : rlCheck (opsP 5 133) HNSeed1 HNSeed2 hnrlNregs hnrlProg hnrlSpec
    hnrlTabs = true := by
  have h := KernelAM.hnRank_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨vA, vB⟩, h⟩ := h
  have hA : (opsP 5 133).decode NativeSporadic.HNSeed1 =
      (homP kConsts (by norm_num)).U (pay HS1.chars) := by
    rw [HS1.eq]
    exact CFSG.KS.SporSch.LyM.payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)
  have hB : (opsP 5 133).decode NativeSporadic.HNSeed2 =
      (homP kConsts (by norm_num)).U (pay HS2.chars) := by
    rw [HS2.eq]
    exact CFSG.KS.SporSch.LyM.payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)
  have hD := KernelAM.hnRank_D
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hD
  obtain ⟨⟨⟨hrA, hrB⟩, hwf⟩, hlin⟩ := hD
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (homP kConsts (by norm_num)) hA hB vA vB hrA hrB h
  unfold rlCheck
  rw [hm, h0, h1, hwf, hlin]
  simp [hrA, hrB]

end Certificates
