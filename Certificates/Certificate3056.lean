
module

public import Certificates.Certificate3056Base

public import CFSG.Monster.B.TwoA.Co2Inv.SixCertInputs
public import Certificates.Kernel.MonsterB.Six3056K
public import CFSG.Certificates.Kernel.MonsterB.QFormSound
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.TwoA.Co2Inv CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.QForm CFSG.KC.Bfs
  CertificateChecks.Six3056

namespace CertificateChecks.Batch3056

open CFSG.Monster.B.TwoA.Co2Inv CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.QForm CFSG.KC.Bfs
  CertificateChecks.Six3056

set_option maxRecDepth 100000

end CertificateChecks.Batch3056

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Co2Inv in
theorem certificate3056 : sixCheck = true := CertificateChecks.Batch3056.six

end Certificates
