module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.GLQ.HNTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaHNRankData
public import Certificates.Data.ONanD2HNE125
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CertificateChecks.KernelGLQ.HNTwo

theorem hnRank_K : forceB (pay HS1.chars) (fun A => forceB (pay HS2.chars) fun B =>
    vld A && vld B && regsN O5 A B AlphaHNRank.hnrlNregs AlphaHNRank.hnrlProg
      (fun R => certN O5 R ⟨AlphaHNRank.hnrlNregs, AlphaHNRank.hnrlProg,
          AlphaHNRank.hnrlSpec.facts⟩ &&
        O5.eq (getN R AlphaHNRank.hnrlSpec.rA) A && O5.eq (getN R AlphaHNRank.hnrlSpec.rB) B)) =
    true := by
  quickRfl

theorem hnRank_D : (decide (AlphaHNRank.hnrlSpec.rA < AlphaHNRank.hnrlNregs) &&
    decide (AlphaHNRank.hnrlSpec.rB < AlphaHNRank.hnrlNregs) &&
    AlphaHNRank.hnrlSpec.wf && AlphaHNRank.hnrlSpec.linOK AlphaHNRank.hnrlTabs) = true := by
  decide +kernel

theorem hnE125_K : forceB (pay HS1.chars) (fun A => forceB (pay HS2.chars) fun B =>
    vld A && vld B && mcertN O5 A B AlphaHNE125.hnE125Cert) = true := by
  quickRfl

theorem hnE125_D : AlphaHNE125.hnE125Mod.wf 5 = true := by
  decide +kernel

end CertificateChecks.KernelAM

end
