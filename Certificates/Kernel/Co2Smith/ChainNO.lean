module

public import Certificates.Kernel.Co2Smith.ChainNData
public import Certificates.Kernel.Sporadic.RawGenSchO

public section

namespace CertificateChecks.KernelCo2Smith

@[expose] def chNOW : List (List Nat) :=
  [[1, 0, 1, 1, 0, 1, 1, 2, 0, 1, 1, 2, 0, 2, 1, 2, 1, 0, 1, 2, 1], [0], [1, 0, 1, 1, 1, 1, 1, 1, 1],
   [1, 0, 1, 2, 1, 1, 2, 1, 0, 2, 0, 2, 1, 1, 2, 1, 1, 1, 2],
   [1, 2, 1, 1, 2, 1, 1, 2, 1, 0, 2, 1, 1, 2, 1, 1, 2], [1, 0, 1, 1, 1, 1, 1, 0, 1, 1],
   [2, 0, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 2], [1, 1, 1, 1, 0, 1, 1, 1, 1, 0],
   [1, 1, 1, 2, 0, 2, 0, 2, 0, 1, 1, 1, 1, 1], [1], [2]]

end CertificateChecks.KernelCo2Smith

set_option maxRecDepth 400000

#ks_rawchain_sl2_osub CertificateChecks.KernelCo2Smith.CN 1 9 10
  CertificateChecks.KernelCo2Smith.chNOW
