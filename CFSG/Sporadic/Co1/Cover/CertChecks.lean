module

public import CFSG.Sporadic.Co1.Cover.Fox
public import Certificates.Certificate10060
public meta import CFSG.Sporadic.Co1.Cover.Fox
public meta import CFSG.Sporadic.Co1.Cover.Data
public meta import CFSG.Monster.Schur.M24.Words

public section

namespace CFSG.Sporadic.Co1.Cover

open CFSG.Sporadic.SmallF2 Matrix

theorem fox_cert :
    deltaMat Amat Bmat * listMat foxXrows 11 (11 + 11) +
    yMat * foxMatC + zMat * lamMat (toVecD 11 x0mask) = 1 :=
  Certificates.certificate10060.1

theorem hl_cert :
    listMat clX1 11 11 * (Amatᵀ - 1) + listMat clX2 11 11 * (Bmatᵀ - 1) = 1 :=
  Certificates.certificate10060.2.1

theorem hC_cert :
    bigMat cSsym * Rsym + bigMat cSdiag * Rdiag + bigMat cSA * Rinv Amat +
    bigMat cSB * Rinv Bmat = 1 :=
  Certificates.certificate10060.2.2.1

theorem Amat_x0 : Amat *ᵥ toVecD 11 x0mask = toVecD 11 x0mask :=
  Certificates.certificate10060.2.2.2

end CFSG.Sporadic.Co1.Cover
