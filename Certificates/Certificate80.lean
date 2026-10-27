module

public import CFSG.LieType.Steinberg.Adjoint.Cert
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate117

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch80

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

private theorem e8Data_checkPairs_0 : e8Data.checkPairsRange 0 20 = true := by decide +kernel
private theorem e8Data_checkPairs_1 : e8Data.checkPairsRange 20 20 = true := by decide +kernel
private theorem e8Data_checkPairs_2 : e8Data.checkPairsRange 40 20 = true := by decide +kernel
private theorem e8Data_checkPairs_3 : e8Data.checkPairsRange 60 20 = true := by decide +kernel
private theorem e8Data_checkPairs_4 : e8Data.checkPairsRange 80 20 = true := by decide +kernel
private theorem e8Data_checkPairs_5 : e8Data.checkPairsRange 100 20 = true := by decide +kernel
private theorem e8Data_checkPairs_6 : e8Data.checkPairsRange 120 20 = true := by decide +kernel
private theorem e8Data_checkPairs_7 : e8Data.checkPairsRange 140 20 = true := by decide +kernel
private theorem e8Data_checkPairs_8 : e8Data.checkPairsRange 160 20 = true := by decide +kernel
private theorem e8Data_checkPairs_9 : e8Data.checkPairsRange 180 20 = true := by decide +kernel
private theorem e8Data_checkPairs_10 : e8Data.checkPairsRange 200 20 = true := by decide +kernel
private theorem e8Data_checkPairs_11 : e8Data.checkPairsRange 220 20 = true := by decide +kernel

end CertificateChecks.Batch80

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
theorem certificate80 : (e8Data.checkPairsRange 0 20 = true)
    ∧ (e8Data.checkPairsRange 20 20 = true)
    ∧ (e8Data.checkPairsRange 40 20 = true)
    ∧ (e8Data.checkPairsRange 60 20 = true)
    ∧ (e8Data.checkPairsRange 80 20 = true)
    ∧ (e8Data.checkPairsRange 100 20 = true)
    ∧ (e8Data.checkPairsRange 120 20 = true)
    ∧ (e8Data.checkPairsRange 140 20 = true)
    ∧ (e8Data.checkPairsRange 160 20 = true)
    ∧ (e8Data.checkPairsRange 180 20 = true)
    ∧ (e8Data.checkPairsRange 200 20 = true)
    ∧ (e8Data.checkPairsRange 220 20 = true) := by
  exact ⟨CertificateChecks.Batch80.e8Data_checkPairs_0, CertificateChecks.Batch80.e8Data_checkPairs_1, CertificateChecks.Batch80.e8Data_checkPairs_2, CertificateChecks.Batch80.e8Data_checkPairs_3, CertificateChecks.Batch80.e8Data_checkPairs_4, CertificateChecks.Batch80.e8Data_checkPairs_5, CertificateChecks.Batch80.e8Data_checkPairs_6, CertificateChecks.Batch80.e8Data_checkPairs_7, CertificateChecks.Batch80.e8Data_checkPairs_8, CertificateChecks.Batch80.e8Data_checkPairs_9, CertificateChecks.Batch80.e8Data_checkPairs_10, CertificateChecks.Batch80.e8Data_checkPairs_11⟩

end Certificates
