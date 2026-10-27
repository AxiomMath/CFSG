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

meta def sU : Array (Array Nat) := strongL [0, 2, 4, 6] Certificates.AE6CertEK.dU

meta def sP1 : Array (Array Nat) := strongL [0, 1, 2, 4, 6] Certificates.AE6CertEK.dP1

meta def sP3 : Array (Array Nat) := strongL [0, 2, 3, 4, 6] Certificates.AE6CertEK.dP3

meta def sP5 : Array (Array Nat) := strongL [0, 2, 4, 5, 6] Certificates.AE6CertEK.dP5

meta def bU : Array Nat := #[0, 2, 4, 24, 8]

meta def bP3 : Array Nat := #[0, 2, 1, 4, 24, 8]

end CertificateChecks.KernelAE6CertE

#ks_rawchain CertificateChecks.KernelAE6CertE.U 360 9 24 CertificateChecks.KernelAE6CertE.sU
  CertificateChecks.KernelAE6CertE.bU 4 Certificates.AE6CertEK.dU

#ks_rawchain CertificateChecks.KernelAE6CertE.P1 360 9 24 CertificateChecks.KernelAE6CertE.sP1
  CertificateChecks.KernelAE6CertE.bU 5 Certificates.AE6CertEK.dP1

#ks_rawchain CertificateChecks.KernelAE6CertE.P3 360 9 24 CertificateChecks.KernelAE6CertE.sP3
  CertificateChecks.KernelAE6CertE.bP3 5 Certificates.AE6CertEK.dP3

#ks_rawchain CertificateChecks.KernelAE6CertE.P5 360 9 24 CertificateChecks.KernelAE6CertE.sP5
  CertificateChecks.KernelAE6CertE.bU 5 Certificates.AE6CertEK.dP5

end
