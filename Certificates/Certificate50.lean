module

public import CFSG.LieType.Chevalley.RootOps.Instance
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch50

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e6_conjRange_0_72 : conjRange .E6 0 72 = true := by decide +kernel

end CertificateChecks.Batch50

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate50 : (conjRange .E6 0 72 = true) := by
  exact CertificateChecks.Batch50.e6_conjRange_0_72

end Certificates
