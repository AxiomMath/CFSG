module

public import Certificates.Kernel.Census.M2217.Data
public import Certificates.Data.Kernel.Census.PackedL

public section

namespace CertificateChecks.KernelCensus.M2217

open CFSG.KC.Census

@[expose] noncomputable def nodeL (fl : List Bool) (i : Nat) : Bool :=
  pnodeL2 24 5 [0, 1, 2, 3, 4, 5, 8, 9] (pinXL m2217XS) outXP true false false m2217CS m2217Nodes
    m2217WCS m2217PFS fl i

@[expose] noncomputable def blkL (a len : Nat) : Bool :=
  withFl 24 5 m2217CS fun fl => (List.range' a len).all (nodeL fl)

end CertificateChecks.KernelCensus.M2217

end
