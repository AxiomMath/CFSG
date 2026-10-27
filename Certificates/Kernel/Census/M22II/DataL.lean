module

public import Certificates.Kernel.Census.M22II.Data
public import Certificates.Data.Kernel.Census.PackedL

public section

namespace CertificateChecks.KernelCensus.M22II

open CFSG.KC.Census

@[expose] noncomputable def nodeL (fl : List Bool) (i : Nat) : Bool :=
  pnodeL 24 5 [0, 1, 2, 3, 4, 5, 8, 9] (pinXL m22IIXS) outXP false true false m22IICS m22IINodes
    m22IIWCS fl i

@[expose] noncomputable def blkL (a len : Nat) : Bool :=
  withFl 24 5 m22IICS fun fl => (List.range' a len).all (nodeL fl)

end CertificateChecks.KernelCensus.M22II

end
