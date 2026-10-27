module

public import Certificates.Kernel.TcGen.Suz
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSuzData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM

open CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaSuz

theorem suz_K : mcertL KernelTc.Suz.lay KernelTc.Suz.A KernelTc.Suz.B
    ⟨suzNregs, suzProg, suzMod.modFactsE 3 suzTops suzGs⟩ = true := by
  quickRfl

end CertificateChecks.KernelAM

end
