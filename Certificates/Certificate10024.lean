module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData
import Certificates.Kernel.M12Cover.Fixed10024A
import Certificates.Kernel.M12Cover.Fixed10024B
import Certificates.Kernel.M12Cover.Fixed10024C

public section

namespace Certificates

open CertificateChecks.KernelM12Cover in
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier in
theorem certificate10024 :
    (checkChainD = true)
    ∧ (checkFour (enumeration fixedDQ) = true)
    ∧ (checkInvolutions (enumeration fixedDQ) = true)
    ∧ (checkConj (enumeration fixedDQ) = true)
    ∧ (checkKernel (enumeration fixedDQ) = true)
    ∧ (checkPairs (enumeration fixedDQ) = true)
    ∧ (checkCount (enumeration fixedDQ) = true)
    ∧ (checkFourMul = true)
    ∧ (checkFourInv = true)
    ∧ (checkFourAbelian = true)
    ∧ (checkFourDistinctEntries = true)
    ∧ (checkFourSeparated = true)
    ∧ (checkFourArrays = true)
    ∧ (checkFourWords = true)
    ∧ (checkFourIndex = true) :=
  ⟨checkChainD_eq, checkFour_eq, checkInvolutions_eq, checkConj_eq, checkKernel_eq,
    checkPairs_eq, checkCount_eq, checkFourMul_eq, checkFourInv_eq, checkFourAbelian_eq,
    checkFourDistinctEntries_eq, checkFourSeparated_eq, checkFourArrays_eq, checkFourWords_eq,
    checkFourIndex_eq⟩

end Certificates
