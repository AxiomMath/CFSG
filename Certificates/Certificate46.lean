module

public import CFSG.LieType.Chevalley.RootOps.Instance
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch46

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem d4_conjRange_0_24 : conjRange .D4 0 24 = true := by decide +kernel

end CertificateChecks.Batch46

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate46 : (conjRange .D4 0 24 = true) := by
  exact CertificateChecks.Batch46.d4_conjRange_0_24

end Certificates
