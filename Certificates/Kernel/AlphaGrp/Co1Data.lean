module

public import Certificates.Data.Kernel.AlphaWfK
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaCo1Data

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelAG

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.AlphaCo1

theorem co1_wfK : co1Mod.wfK 3 = true := by
  decide +kernel

theorem co1_pcWf : pcWf (co1Tops ++ co1Mod.basisPc 3) = true := by
  decide +kernel

theorem co1_mats : co1Mod.acts.all (fun g => g.mat.all (· < 3)) = true := by
  decide +kernel

theorem co1_tops : co1Tops.all (fun q => co1Mod.acts.any (·.reg == q.reg)) = true := by
  decide +kernel

theorem co1_grpOK : co1Mod.grpOK co1Tops co1Gs = true := by
  decide +kernel

theorem co1_rank : decide (3 ≤ co1Mod.basis.length) = true := by
  decide +kernel

end CertificateChecks.KernelAG
