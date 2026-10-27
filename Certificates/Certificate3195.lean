
module

public import Certificates.Certificate3195Base

import Certificates.Kernel.UnitarySix.SU42Card

public section

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaPar in
theorem certificate3195 : Nat.card suClosure = 25920 :=
  KernelU6.card_suClosure

end Certificates
