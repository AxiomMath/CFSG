module

public import CFSG.LieType.Steinberg.Adjoint.CertE6Inputs
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate117

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch118

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

private theorem e6AdjData_checkTables : e6AdjData.checkTables = true := by decide +kernel

private theorem e6AdjData_checkSimple : e6AdjData.checkSimple = true := by decide +kernel

private theorem e6AdjData_checkPairNorm : e6AdjData.checkPairNorm = true := by decide +kernel

end CertificateChecks.Batch118

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
theorem certificate118 : (e6AdjData.checkTables = true)
    ∧ (e6AdjData.checkSimple = true)
    ∧ (e6AdjData.checkPairNorm = true) := by
  exact ⟨CertificateChecks.Batch118.e6AdjData_checkTables, CertificateChecks.Batch118.e6AdjData_checkSimple, CertificateChecks.Batch118.e6AdjData_checkPairNorm⟩

end Certificates
