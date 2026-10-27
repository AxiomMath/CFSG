module

public import CFSG.LieType.Steinberg.Adjoint.CertE7Data
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate117

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch79

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

private theorem e7AdjData_checkWeyl_0 : e7AdjData.checkWeylRange 0 18 = true := by
  decide +kernel

private theorem e7AdjData_checkWeyl_1 : e7AdjData.checkWeylRange 18 18 = true := by
  decide +kernel

private theorem e7AdjData_checkWeyl_2 : e7AdjData.checkWeylRange 36 18 = true := by
  decide +kernel

private theorem e7AdjData_checkWeyl_3 : e7AdjData.checkWeylRange 54 18 = true := by
  decide +kernel

private theorem e7AdjData_checkWeyl_4 : e7AdjData.checkWeylRange 72 18 = true := by
  decide +kernel

private theorem e7AdjData_checkWeyl_5 : e7AdjData.checkWeylRange 90 18 = true := by
  decide +kernel

private theorem e7AdjData_checkWeyl_6 : e7AdjData.checkWeylRange 108 18 = true := by
  decide +kernel

end CertificateChecks.Batch79

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
theorem certificate79 : (e7AdjData.checkWeylRange 0 18 = true)
    ∧ (e7AdjData.checkWeylRange 18 18 = true)
    ∧ (e7AdjData.checkWeylRange 36 18 = true)
    ∧ (e7AdjData.checkWeylRange 54 18 = true)
    ∧ (e7AdjData.checkWeylRange 72 18 = true)
    ∧ (e7AdjData.checkWeylRange 90 18 = true)
    ∧ (e7AdjData.checkWeylRange 108 18 = true) := by
  exact ⟨CertificateChecks.Batch79.e7AdjData_checkWeyl_0, CertificateChecks.Batch79.e7AdjData_checkWeyl_1, CertificateChecks.Batch79.e7AdjData_checkWeyl_2, CertificateChecks.Batch79.e7AdjData_checkWeyl_3, CertificateChecks.Batch79.e7AdjData_checkWeyl_4, CertificateChecks.Batch79.e7AdjData_checkWeyl_5, CertificateChecks.Batch79.e7AdjData_checkWeyl_6⟩

end Certificates
