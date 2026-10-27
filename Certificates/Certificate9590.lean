module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaONData
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaMc.F3
import CFSG.Certificates.Kernel.OpsLayMcertSound

public section

set_option maxRecDepth 400000

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaON
  CFSG.Blueprint

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaON
  CFSG.Blueprint.NativeSporadic in
theorem certificate9590 : absCheck (ops3 154) ONSeed1 ONSeed2 onNregs onProg 3 onMod onCf onCi onCt onQ 0 1 = true := by
  unfold absCheck
  rw [mcertL_sound (d := 154) KernelAM.ON.lay_ok rfl rfl KernelAM.ON.decA KernelAM.ON.decB KernelAM.ON.LA_eq
    KernelAM.ON.LB_eq KernelAM.on_K, Bool.true_and]
  exact KernelAM.on_D

end Certificates
