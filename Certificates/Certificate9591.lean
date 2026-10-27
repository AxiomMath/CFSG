module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaMcLData
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaMc.F3
import CFSG.Certificates.Kernel.OpsLayMcertSound

public section

set_option maxRecDepth 400000

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaMcL
  CFSG.Blueprint

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaMcL
  CFSG.Blueprint.NativeSporadic in
theorem certificate9591 : modCheck (ops3 21) McLSeed1 McLSeed2 mclNregs mclProg 3 mclMod mclTops mclTests
    mclCf mclCi mclCt = true := by
  unfold modCheck
  rw [mcertL_sound (d := 21) KernelAM.McL.lay_ok rfl rfl KernelAM.McL.decA KernelAM.McL.decB
    KernelAM.McL.LA_eq KernelAM.McL.LB_eq KernelAM.mcl_K, Bool.true_and]
  exact KernelAM.mcl_D

end Certificates
