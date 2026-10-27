module

public import CFSG.LieType.Steinberg.Adjoint.CertE6
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate117
import Certificates.Certificate118

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch76

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

private theorem e6AdjData_checkPairs_0 : e6AdjData.checkPairsRange 0 24 = true := by decide +kernel
private theorem e6AdjData_checkPairs_1 : e6AdjData.checkPairsRange 24 24 = true := by decide +kernel
private theorem e6AdjData_checkPairs_2 : e6AdjData.checkPairsRange 48 24 = true := by decide +kernel

end CertificateChecks.Batch76

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
theorem certificate76 : (e6AdjData.checkPairsRange 0 24 = true)
    ∧ (e6AdjData.checkPairsRange 24 24 = true)
    ∧ (e6AdjData.checkPairsRange 48 24 = true) := by
  exact ⟨CertificateChecks.Batch76.e6AdjData_checkPairs_0, CertificateChecks.Batch76.e6AdjData_checkPairs_1, CertificateChecks.Batch76.e6AdjData_checkPairs_2⟩

end Certificates
