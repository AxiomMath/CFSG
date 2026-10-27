module

public import CFSG.Monster.Existence.Co1BridgeDataInputs
public import CFSG.Monster.VisCert.FrameData
public import Certificates.Data.CFSGNative.Co1.Data

public section

open CFSG.Monster.VisCert CFSG.Sporadic.SmallF2.Native CFSG.Monster.Existence.Co1Bridge

namespace CertificateChecks.Batch8955

open CFSG.Monster.VisCert CFSG.Sporadic.SmallF2.Native CFSG.Monster.Existence.Co1Bridge

private theorem transposeRows_rowsA_0 :
    transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsA = atRows := by
  decide +kernel

private theorem transposeRows_rowsB_0 :
    transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB = btRows := by
  decide +kernel

private theorem rowsA_sq_0 : mulRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsA
    CFSG.Sporadic.Co1.Native.co1Data.rowsA = idRows 24 := by
  decide +kernel

private theorem rowsB_cube_0 : mulRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB
    (mulRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB CFSG.Sporadic.Co1.Native.co1Data.rowsB) =
      idRows 24 := by
  decide +kernel

private theorem mulRows_e_eInv_0 : mulRows 24 eRows eInvRows = idRows 24 := by
  decide +kernel

private theorem mulRows_eInv_e_0 : mulRows 24 eInvRows eRows = idRows 24 := by
  decide +kernel

private theorem xWord_lt_0 : ∀ g ∈ xWord, g < 15 := by
  decide +kernel

private theorem yWord_lt_0 : ∀ g ∈ yWord, g < 15 := by
  decide +kernel

private theorem xCheck_0 : ∀ i < 24, actWord frameMatrices xWord (vecMulN 24 eRows (1 <<< i)) =
    vecMulN 24 eRows (vecMulN 24 atRows (1 <<< i)) := by
  decide +kernel

private theorem yCheck_0 : ∀ i < 24, actWord frameMatrices yWord (vecMulN 24 eRows (1 <<< i)) =
    vecMulN 24 eRows (vecMulN 24 btRows (1 <<< i)) := by
  decide +kernel

end CertificateChecks.Batch8955

namespace Certificates

open CertificateChecks

open CFSG.Monster.VisCert CFSG.Sporadic.SmallF2.Native CFSG.Monster.Existence.Co1Bridge in
theorem certificate8955 :
    transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsA = atRows ∧
    transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB = btRows ∧
    mulRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsA
      CFSG.Sporadic.Co1.Native.co1Data.rowsA = idRows 24 ∧
    mulRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB
      (mulRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB CFSG.Sporadic.Co1.Native.co1Data.rowsB) =
        idRows 24 ∧
    mulRows 24 eRows eInvRows = idRows 24 ∧
    mulRows 24 eInvRows eRows = idRows 24 ∧
    (∀ g ∈ xWord, g < 15) ∧
    (∀ g ∈ yWord, g < 15) ∧
    (∀ i < 24, actWord frameMatrices xWord (vecMulN 24 eRows (1 <<< i)) =
      vecMulN 24 eRows (vecMulN 24 atRows (1 <<< i))) ∧
    ∀ i < 24, actWord frameMatrices yWord (vecMulN 24 eRows (1 <<< i)) =
      vecMulN 24 eRows (vecMulN 24 btRows (1 <<< i)) := by
  exact ⟨CertificateChecks.Batch8955.transposeRows_rowsA_0, CertificateChecks.Batch8955.transposeRows_rowsB_0, CertificateChecks.Batch8955.rowsA_sq_0,
    CertificateChecks.Batch8955.rowsB_cube_0, CertificateChecks.Batch8955.mulRows_e_eInv_0, CertificateChecks.Batch8955.mulRows_eInv_e_0,
    CertificateChecks.Batch8955.xWord_lt_0, CertificateChecks.Batch8955.yWord_lt_0, CertificateChecks.Batch8955.xCheck_0, CertificateChecks.Batch8955.yCheck_0⟩

end Certificates
