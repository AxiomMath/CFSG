module

public import Certificates.Data.Kernel.Co1M.ThirteenScan
public import Certificates.Kernel.Co1M.D16956
public import Certificates.Kernel.VecCert.Co1.Data
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CFSG.KD.C16956

open CFSG.KD.Co1Thirteen CFSG.KC.Co1M CFSG.KC.VecK CertificateChecks.KernelVec.Co1

@[expose] noncomputable def sc16956c (s : Nat) : Bool :=
  scanSl (orbMemK 98280 (lk S 32) 17) (lk Pt 32) TS16956 Q16956 (Nat.add s 192)

end CFSG.KD.C16956

#kc_slices CFSG.KD.C16956.Scan16956c CFSG.KD.C16956.sc16956c 96

end
