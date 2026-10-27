
module

public import Certificates.Certificate3064Base

public import CFSG.Monster.B.TwoA.Base.SevenPairCInputs
public import CFSG.Certificates.Kernel.SortTreeSound
public import Certificates.Kernel.MonsterB.Gl3064Data
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA CFSG.KC.SortTree CFSG.KLie.CT

namespace CertificateChecks.Batch3064

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

end CertificateChecks.Batch3064

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA in
theorem certificate3064 : (natCertOK actW2 2 (fun m => decide (m < 16)) (codeMat 2 1) glCert2 = true)
    ∧ (natCertOK actW3 5 (fun m => decide (m < 512)) (codeMat 3 1) glCert3 = true)
    ∧ (glCert2.pts.size = 6)
    ∧ (glCert3.pts.size = 168) :=
  ⟨CertificateChecks.Batch3064.c2.1, CertificateChecks.Batch3064.c3.1, CertificateChecks.Batch3064.c2.2, CertificateChecks.Batch3064.c3.2⟩

end Certificates
