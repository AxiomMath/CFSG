module

public import Certificates.Kernel.Co2Smith.ChainG0Data
public import Certificates.Kernel.Sporadic.RawGenSchO

public section

namespace CertificateChecks.KernelCo2Smith

@[expose] def chG0OW : List (List Nat) :=
  [[3, 1, 0, 1, 0, 1, 0, 3], [0, 2, 3, 0, 1, 3, 0, 3, 1, 0, 2, 3, 2, 1, 3, 0, 3, 1, 3],
   [0, 2, 3, 0, 1, 2, 3, 0, 1, 0, 1, 0, 3, 2, 1, 0, 1, 3, 2, 0, 3, 1, 3],
   [1, 3, 1, 3, 0, 1, 0, 2, 0, 1, 0, 1, 3, 0, 2, 3, 2, 0, 1, 3], [2, 3, 1, 3, 0, 3, 1, 3, 0, 2, 0],
   [2, 0, 3, 0, 2, 0, 1, 3, 0, 2, 1, 3, 0, 3, 2, 1, 0, 3, 1, 0, 2, 0, 3, 0, 2],
   [3, 1, 3, 0, 3, 2, 1, 3, 2, 1, 3, 0, 3, 1, 3, 2, 0], [0],
   [1, 0, 1, 0, 2, 0, 1, 0, 1, 3, 1, 0, 1, 0, 2, 1, 3, 2, 0, 3],
   [0, 1, 0, 3, 0, 1, 0, 3, 1, 0, 3, 0, 1, 3, 0, 1, 0, 3, 0, 1, 0, 3], [1], [2], [3]]

end CertificateChecks.KernelCo2Smith

set_option maxRecDepth 400000

#ks_rawchain_sl2_osub CertificateChecks.KernelCo2Smith.CG0 7 10 11 12
  CertificateChecks.KernelCo2Smith.chG0OW
