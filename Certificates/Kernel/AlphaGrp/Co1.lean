module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.AlphaFunK
public import Certificates.Kernel.AlphaMc.SeedsF2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaCo1Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAG

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo1

theorem co1_K : mcertN (opsF2K 24) KernelAM.C1A.M KernelAM.C1B.M
    ⟨co1Nregs, co1Prog, co1Mod.modFactsE 3 co1Tops co1Gs⟩ = true := by
  quickRfl

theorem co1_fun : funW 3 co1Mod 6 29 1044 co1CfSp = true := by decide +kernel

theorem co1_alt : altW 3 co1Mod 6 29 37584 1296 co1CiSp [] tgtAlt = true := by decide +kernel

end CertificateChecks.KernelAG

end
