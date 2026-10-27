module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigSig
import Certificates.Kernel.HSStd.U43I4Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43 in
theorem certificate27275 : ∀ {y c k : Equiv.Perm (Fin 820)},
    SigRel (rP 5) y c k → y ∈ R → c ∈ R → k ∈ R → False := by
  intro y c k hs hy hc hk
  obtain ⟨u, hu, h5⟩ := KernelHSStd.U43I4.u5_facts
  exact KernelHSStd.U43I4.false_rP5_of_rP4 hu h5
    (fun h1 h2 h3 h4 => KernelHSStd.U43I4.i4_false h1 h2 h3 h4) hs hy hc hk

end Certificates
