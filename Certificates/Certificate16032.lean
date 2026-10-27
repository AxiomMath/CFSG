module

public import CFSG.Sporadic.Co2Smith.ResSpInputs
public import Certificates.Certificate16039
public import Certificates.Data.CFSGNative.Co2Smith.Check

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix CFSG.Assembly.LowTwoRank
open scoped Matrix

namespace CertificateChecks.Batch16032

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix CFSG.Assembly.LowTwoRank
open scoped Matrix

private theorem colsA_sp_0 : (colsMat Native.colsA)ᵀ * spJ * colsMat Native.colsA = spJ := by
  decide +kernel

private theorem colsB_sp_1 : (colsMat Native.colsB)ᵀ * spJ * colsMat Native.colsB = spJ := by
  decide +kernel

end CertificateChecks.Batch16032

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem certificate16032 : (
    (colsMat Native.colsA)ᵀ * spJ * colsMat Native.colsA = spJ
  ) ∧ (
    (colsMat Native.colsB)ᵀ * spJ * colsMat Native.colsB = spJ
  ) := by
  exact ⟨CertificateChecks.Batch16032.colsA_sp_0, CertificateChecks.Batch16032.colsB_sp_1⟩

end Certificates
