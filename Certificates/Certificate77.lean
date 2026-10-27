module

public import CFSG.LieType.Steinberg.Adjoint.CertE6
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate117
import Certificates.Certificate118

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch77

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

private theorem e6AdjData_checkWeyl_0 : e6AdjData.checkWeylRange 0 24 = true := by decide +kernel
private theorem e6AdjData_checkWeyl_1 : e6AdjData.checkWeylRange 24 24 = true := by decide +kernel
private theorem e6AdjData_checkWeyl_2 : e6AdjData.checkWeylRange 48 24 = true := by decide +kernel

end CertificateChecks.Batch77

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
theorem certificate77 : (e6AdjData.checkWeylRange 0 24 = true)
    ∧ (e6AdjData.checkWeylRange 24 24 = true)
    ∧ (e6AdjData.checkWeylRange 48 24 = true) := by
  exact ⟨CertificateChecks.Batch77.e6AdjData_checkWeyl_0, CertificateChecks.Batch77.e6AdjData_checkWeyl_1, CertificateChecks.Batch77.e6AdjData_checkWeyl_2⟩

end Certificates
