module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIL34Data
import Certificates.Kernel.HSStd.L34CentGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HSStd.HFI in
theorem certificate27219 : hfi34Check (enumBFS 42 gTabs 241920).tabs
    (CFSG.PSL3Four.Native.orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₃T 1963).tabs = true := KernelHSStd.L34C.hfi34_true

end Certificates
