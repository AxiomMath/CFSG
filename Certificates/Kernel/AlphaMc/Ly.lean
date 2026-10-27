module

public import Certificates.Kernel.MatCert.Ly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaLyRankData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CertificateChecks.KernelSporSch CertificateChecks.KernelMC
  CFSG.AGLEmbedding.R3.AlphaLyRank

theorem lyRank_K : regsN OL LyBS.A LyBS.B lyrlNregs lyrlProg (fun R =>
    certN OL R ⟨lyrlNregs, lyrlProg, lyrlSpec.facts⟩ &&
      OL.eq (getN R 0) LyBS.A && OL.eq (getN R 1) LyBS.B &&
      (List.range 5).all (fun j => decide ((lyrlSpec.gen.els.getD j default).reg < lyrlNregs) &&
        OL.eq (getN R (lyrlSpec.gen.els.getD j default).reg) (LySv.AF (j + 2))) &&
      decide (lyrlSpec.gen.rs < lyrlNregs) && notStabL (getN R lyrlSpec.gen.rs)) = true := by
  quickRfl

theorem lyRank_D : (decide (lyrlSpec.gen.els.length = 5) && lyrlSpec.wf &&
    lyrlSpec.linOK lyrlTabs) = true := by
  decide +kernel

end CertificateChecks.KernelAM

end
