module

public import Certificates.Kernel.VecCert.Co1.Data
public import Certificates.Kernel.Co1M.Data10076
public import CFSG.Certificates.Kernel.Co1M.OrbitMem

public section

namespace CFSG.KD.Co1M

open CFSG.KC.VecK CFSG.KC.Co1M CertificateChecks.KernelVec.Co1

@[expose] noncomputable def mclF76 (p : Nat) : Bool :=
  !(orbMemK 98280 (lk S 32) 17 (16663704 ^^^ lk Pt 32 p) &&
      orbMemK 98280 (lk S 32) 17 (lk Pt 32 p ^^^ (16663704 ^^^ 4852818))) ||
    ML.contains (lk Pt 32 p)

@[expose] noncomputable def mclSl76 (s : Nat) : Bool :=
  allS (Nat.mul s 256) (sliceN 98280 256 s) mclF76

end CFSG.KD.Co1M

end
