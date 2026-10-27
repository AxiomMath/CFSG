module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIM12Data
import Certificates.Kernel.HSStd.M12PinGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HSStd.HFI in
theorem certificate27220 : hfiM12Check (enumBFS 12 m12Gens 95040)
    (CFSG.PSL3Four.Native.orbitBFS 12 m12Gens (m12Gens.map (invTab 12)) m12a₀T 891)
    (CFSG.PSL3Four.Native.orbitBFS 12 m12Gens (m12Gens.map (invTab 12)) m12b₀T 891) = true := KernelHSStd.M12K.hfiM12_true

end Certificates
