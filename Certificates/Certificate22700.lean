module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCertInputs
import Certificates.Kernel.LocalComp.HeGSX
import Certificates.Kernel.LocalComp.HeFixBind

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Enum CFSG.KS CFSG.KC.PermTool CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.ComponentClassification.GrSLit.HeGS
open CertificateChecks.KernelLC.HeFix

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix
  CFSG.ComponentClassification.GrSLit.HeGS in
theorem certificate22700 :
    hfCTab (hfRep 12 heGSXWord) = idTab 8330 := by
  have hl : ∀ j ∈ hfRep 12 heGSXWord, j < 9 := by decide
  unfold hfCTab
  rw [wordTabS_unpack hid hidA _ (fun k hk => cnC1 (hl k hk)) (fun k hk => c1Tab_eq (hl k hk)),
    Nat.eq_of_beq_eq_true KernelLC.HeGSX.kX12, idTab_eq, hidA]

end Certificates

end
