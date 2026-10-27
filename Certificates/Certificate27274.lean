module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigSig
import Certificates.Kernel.HSStd.U43I4Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43 in
theorem certificate27274 : ∀ {y c k : Equiv.Perm (Fin 820)},
    SigRel (rP 4) y c k → y ∈ R → c ∈ R → k ∈ R → False :=
  fun hs hy hc hk => KernelHSStd.U43I4.i4_false hs hy hc hk

end Certificates
