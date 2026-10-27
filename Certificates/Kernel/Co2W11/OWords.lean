module

public import Certificates.Data.Kernel.F2OrbW
public import Certificates.Kernel.Co2W11.OWordsData
public import Certificates.Kernel.LocalComp.Co2Ops
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2W11

open CFSG.KC.F2OrbW CertificateChecks.KernelLC.Co2Ops

theorem owords_ok : wordsToK 22 SA.M SB.M 40 (Ow.ts.zip Ow.ws) = true := by quickRfl

end CertificateChecks.KernelCo2W11

end
