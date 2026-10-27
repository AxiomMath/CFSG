module

public import CFSG.LieType.Steinberg.Adjoint.Cert
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate117

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch81

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

private theorem e8Data_checkWeyl_0 : e8Data.checkWeylRange 0 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_1 : e8Data.checkWeylRange 20 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_2 : e8Data.checkWeylRange 40 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_3 : e8Data.checkWeylRange 60 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_4 : e8Data.checkWeylRange 80 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_5 : e8Data.checkWeylRange 100 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_6 : e8Data.checkWeylRange 120 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_7 : e8Data.checkWeylRange 140 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_8 : e8Data.checkWeylRange 160 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_9 : e8Data.checkWeylRange 180 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_10 : e8Data.checkWeylRange 200 20 = true := by decide +kernel
private theorem e8Data_checkWeyl_11 : e8Data.checkWeylRange 220 20 = true := by decide +kernel

end CertificateChecks.Batch81

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
theorem certificate81 : (e8Data.checkWeylRange 0 20 = true)
    ∧ (e8Data.checkWeylRange 20 20 = true)
    ∧ (e8Data.checkWeylRange 40 20 = true)
    ∧ (e8Data.checkWeylRange 60 20 = true)
    ∧ (e8Data.checkWeylRange 80 20 = true)
    ∧ (e8Data.checkWeylRange 100 20 = true)
    ∧ (e8Data.checkWeylRange 120 20 = true)
    ∧ (e8Data.checkWeylRange 140 20 = true)
    ∧ (e8Data.checkWeylRange 160 20 = true)
    ∧ (e8Data.checkWeylRange 180 20 = true)
    ∧ (e8Data.checkWeylRange 200 20 = true)
    ∧ (e8Data.checkWeylRange 220 20 = true) := by
  exact ⟨CertificateChecks.Batch81.e8Data_checkWeyl_0, CertificateChecks.Batch81.e8Data_checkWeyl_1, CertificateChecks.Batch81.e8Data_checkWeyl_2, CertificateChecks.Batch81.e8Data_checkWeyl_3, CertificateChecks.Batch81.e8Data_checkWeyl_4, CertificateChecks.Batch81.e8Data_checkWeyl_5, CertificateChecks.Batch81.e8Data_checkWeyl_6, CertificateChecks.Batch81.e8Data_checkWeyl_7, CertificateChecks.Batch81.e8Data_checkWeyl_8, CertificateChecks.Batch81.e8Data_checkWeyl_9, CertificateChecks.Batch81.e8Data_checkWeyl_10, CertificateChecks.Batch81.e8Data_checkWeyl_11⟩

end Certificates
