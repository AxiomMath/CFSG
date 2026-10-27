module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Data
import Certificates.Kernel.HSStd.L34CentGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HSStd.HL34 in
theorem certificate27218 : hl34Check (enumBFS 42 gTabs 241920).tabs
    (CFSG.PSL3Four.Native.orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₂T 1963).tabs
    (CFSG.PSL3Four.Native.orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₄T 1963).tabs = true := KernelHSStd.L34C.hl34_true

end Certificates
