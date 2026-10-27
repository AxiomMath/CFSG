module

public import Certificates.Kernel.Census.Co2R.Data
public import Certificates.Data.Kernel.Census.PackedConjL

public section

namespace CertificateChecks.KernelCensus.Co2R

open CFSG.KC.Census

@[expose] noncomputable def rootChunkL (m W : Nat) (r : RootR) (S c : Nat) : Bool :=
  prootsL m 5 W r.d.nodes r.d.cs r.d.ci (((r.d.us.toList.zip r.d.roots).drop (c * S)).take S)

end CertificateChecks.KernelCensus.Co2R

end
