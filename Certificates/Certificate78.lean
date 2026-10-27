module

public import CFSG.LieType.Steinberg.Adjoint.CertE7Data
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate117

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch78

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

private theorem e7AdjData_checkPairs_0 : e7AdjData.checkPairsRange 0 18 = true := by
  decide +kernel

private theorem e7AdjData_checkPairs_1 : e7AdjData.checkPairsRange 18 18 = true := by
  decide +kernel

private theorem e7AdjData_checkPairs_2 : e7AdjData.checkPairsRange 36 18 = true := by
  decide +kernel

private theorem e7AdjData_checkPairs_3 : e7AdjData.checkPairsRange 54 18 = true := by
  decide +kernel

private theorem e7AdjData_checkPairs_4 : e7AdjData.checkPairsRange 72 18 = true := by
  decide +kernel

private theorem e7AdjData_checkPairs_5 : e7AdjData.checkPairsRange 90 18 = true := by
  decide +kernel

private theorem e7AdjData_checkPairs_6 : e7AdjData.checkPairsRange 108 18 = true := by
  decide +kernel

end CertificateChecks.Batch78

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
theorem certificate78 : (e7AdjData.checkPairsRange 0 18 = true)
    ∧ (e7AdjData.checkPairsRange 18 18 = true)
    ∧ (e7AdjData.checkPairsRange 36 18 = true)
    ∧ (e7AdjData.checkPairsRange 54 18 = true)
    ∧ (e7AdjData.checkPairsRange 72 18 = true)
    ∧ (e7AdjData.checkPairsRange 90 18 = true)
    ∧ (e7AdjData.checkPairsRange 108 18 = true) := by
  exact ⟨CertificateChecks.Batch78.e7AdjData_checkPairs_0, CertificateChecks.Batch78.e7AdjData_checkPairs_1, CertificateChecks.Batch78.e7AdjData_checkPairs_2, CertificateChecks.Batch78.e7AdjData_checkPairs_3, CertificateChecks.Batch78.e7AdjData_checkPairs_4, CertificateChecks.Batch78.e7AdjData_checkPairs_5, CertificateChecks.Batch78.e7AdjData_checkPairs_6⟩

end Certificates
