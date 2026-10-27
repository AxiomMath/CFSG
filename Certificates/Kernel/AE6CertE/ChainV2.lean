module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.Kernel.AE6CertE.Words
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.AE6CertE.Gen
public meta import Certificates.Data.Kernel.AE6CertE.Words
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.AE6CertE.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6CertE

meta def sV2 : Array (Array Nat) := strongL [0, 1, 2, 3, 4, 6, 7] Certificates.AE6CertEK.dV2

meta def bV2 : Array Nat := #[0, 2, 1, 4, 24, 8]

end CertificateChecks.KernelAE6CertE

#ks_rawchain CertificateChecks.KernelAE6CertE.V2 360 9 24 CertificateChecks.KernelAE6CertE.sV2
  CertificateChecks.KernelAE6CertE.bV2 7 Certificates.AE6CertEK.dV2

end
