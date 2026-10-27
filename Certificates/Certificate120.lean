module

public import CFSG.LieType.Steinberg.Adjoint.CertE8Inputs
import Certificates.Certificate80
import Certificates.Certificate81
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate117

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch120

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

private theorem e8Data_nR : AdjData.nR .E8 = 240 := by decide +kernel

end CertificateChecks.Batch120

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
theorem certificate120 : (AdjData.nR .E8 = 240) := by
  exact CertificateChecks.Batch120.e8Data_nR

end Certificates
