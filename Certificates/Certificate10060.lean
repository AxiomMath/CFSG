module

public import CFSG.Sporadic.Co1.Cover.Fox
import Certificates.Kernel.Co1Cover.C10060

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2 Matrix in
theorem certificate10060 :
    (deltaMat Amat Bmat * listMat foxXrows 11 (11 + 11) +
      yMat * foxMatC + zMat * lamMat (toVecD 11 x0mask) = 1)
    ∧ (listMat clX1 11 11 * (Amatᵀ - 1) + listMat clX2 11 11 * (Bmatᵀ - 1) = 1)
    ∧ (bigMat cSsym * Rsym + bigMat cSdiag * Rdiag + bigMat cSA * Rinv Amat +
      bigMat cSB * Rinv Bmat = 1)
    ∧ (Amat *ᵥ toVecD 11 x0mask = toVecD 11 x0mask) := KernelCo1Cover.facts10060

end Certificates
