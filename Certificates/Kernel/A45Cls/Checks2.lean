module

public import Certificates.Data.Kernel.A45Cls.Pair
public import Certificates.Kernel.A45Cls.Cls
public import Certificates.Kernel.A45Cls.Grp

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls

@[expose] def rW : List (List ℕ) :=
  [[1, 1, 2, 0, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1], [1, 0, 1, 0, 1, 2, 1, 1, 0, 1, 1, 2, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 2, 1, 1, 1, 1], [2, 0]]

@[expose] noncomputable def rootP (k : ℕ) : ℕ :=
  [KA.T KA.r0, KB.T KB.r0, K36.T K36.r0, K540.T K540.r0].getD k 0

theorem rootWords : bindWs 45 6 3 KA.G rootP rW 0 = true := by decide +kernel

theorem rootInv : allN 4 (fun k => isInvK 45 6 (rootP k)) = true := by decide +kernel

theorem prodA : prodK 45 6 13 5 CA.N CA.T (KA.T KA.r0) = true := by decide +kernel

end CertificateChecks.KernelA45

end
