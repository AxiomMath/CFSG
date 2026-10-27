module

public import CFSG.Monster.Existence.Co2BridgeDataInputs
public import Certificates.Data.CFSGNative.Co2.Data

public section

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.Existence.Co2Bridge

namespace CertificateChecks.Batch8954

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.Existence.Co2Bridge

private theorem transposeRows_rowsA_0 :
    transposeRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsA = atRows := by
  decide +kernel

private theorem transposeRows_rowsB_0 :
    transposeRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB = btRows := by
  decide +kernel

private theorem rowsA_sq_0 : mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsA
    CFSG.Sporadic.Co2.Native.co2Data.rowsA = idRows 22 := by
  decide +kernel

private theorem rowsB_pow_five_0 : mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
    (mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
      (mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
        (mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
          CFSG.Sporadic.Co2.Native.co2Data.rowsB))) = idRows 22 := by
  decide +kernel

private theorem mulRows_e_eInv_0 : mulRows 22 eRows eInvRows = idRows 22 := by
  decide +kernel

private theorem mulRows_eInv_e_0 : mulRows 22 eInvRows eRows = idRows 22 := by
  decide +kernel

private theorem xWord_lt_0 : ∀ l ∈ xWord, l < 24 := by
  decide +kernel

private theorem yWord_lt_0 : ∀ l ∈ yWord, l < 24 := by
  decide +kernel

private theorem xCheck_0 : ∀ i < 22, actWordQ xWord (vecMulN 22 eRows (1 <<< i)) =
    vecMulN 22 eRows (vecMulN 22 atRows (1 <<< i)) := by
  decide +kernel

private theorem yCheck_0 : ∀ i < 22, actWordQ yWord (vecMulN 22 eRows (1 <<< i)) =
    vecMulN 22 eRows (vecMulN 22 btRows (1 <<< i)) := by
  decide +kernel

end CertificateChecks.Batch8954

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.Existence.Co2Bridge in
theorem certificate8954 :
    transposeRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsA = atRows ∧
    transposeRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB = btRows ∧
    mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsA
      CFSG.Sporadic.Co2.Native.co2Data.rowsA = idRows 22 ∧
    mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
      (mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
        (mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
          (mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
            CFSG.Sporadic.Co2.Native.co2Data.rowsB))) = idRows 22 ∧
    mulRows 22 eRows eInvRows = idRows 22 ∧
    mulRows 22 eInvRows eRows = idRows 22 ∧
    (∀ l ∈ xWord, l < 24) ∧
    (∀ l ∈ yWord, l < 24) ∧
    (∀ i < 22, actWordQ xWord (vecMulN 22 eRows (1 <<< i)) =
      vecMulN 22 eRows (vecMulN 22 atRows (1 <<< i))) ∧
    ∀ i < 22, actWordQ yWord (vecMulN 22 eRows (1 <<< i)) =
      vecMulN 22 eRows (vecMulN 22 btRows (1 <<< i)) := by
  exact ⟨CertificateChecks.Batch8954.transposeRows_rowsA_0, CertificateChecks.Batch8954.transposeRows_rowsB_0, CertificateChecks.Batch8954.rowsA_sq_0,
    CertificateChecks.Batch8954.rowsB_pow_five_0, CertificateChecks.Batch8954.mulRows_e_eInv_0, CertificateChecks.Batch8954.mulRows_eInv_e_0,
    CertificateChecks.Batch8954.xWord_lt_0, CertificateChecks.Batch8954.yWord_lt_0, CertificateChecks.Batch8954.xCheck_0, CertificateChecks.Batch8954.yCheck_0⟩

end Certificates
