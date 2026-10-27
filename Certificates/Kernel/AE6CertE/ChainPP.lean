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

meta def sP7 : Array (Array Nat) := strongL [0, 2, 4, 6, 7] Certificates.AE6CertEK.dP7

meta def sP57 : Array (Array Nat) := strongL [0, 2, 4, 5, 6, 7] Certificates.AE6CertEK.dP57

meta def sP15 : Array (Array Nat) := strongL [0, 1, 2, 4, 5, 6] Certificates.AE6CertEK.dP15

meta def sP17 : Array (Array Nat) := strongL [0, 1, 2, 4, 6, 7] Certificates.AE6CertEK.dP17

meta def bPP : Array Nat := #[0, 2, 4, 24, 8]

end CertificateChecks.KernelAE6CertE

#ks_rawchain CertificateChecks.KernelAE6CertE.P7 360 9 24 CertificateChecks.KernelAE6CertE.sP7
  CertificateChecks.KernelAE6CertE.bPP 5 Certificates.AE6CertEK.dP7

#ks_rawchain CertificateChecks.KernelAE6CertE.P57 360 9 24 CertificateChecks.KernelAE6CertE.sP57
  CertificateChecks.KernelAE6CertE.bPP 6 Certificates.AE6CertEK.dP57

#ks_rawchain CertificateChecks.KernelAE6CertE.P15 360 9 24 CertificateChecks.KernelAE6CertE.sP15
  CertificateChecks.KernelAE6CertE.bPP 6 Certificates.AE6CertEK.dP15

#ks_rawchain CertificateChecks.KernelAE6CertE.P17 360 9 24 CertificateChecks.KernelAE6CertE.sP17
  CertificateChecks.KernelAE6CertE.bPP 6 Certificates.AE6CertEK.dP17

end
