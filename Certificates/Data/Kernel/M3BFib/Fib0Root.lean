module

public import Certificates.Data.Kernel.M3BFib.FibRoot

public section

namespace CFSG.KC.M3BF

open Timmesfeld.M3B (nfD eOf B0 fRootV)

@[expose] noncomputable def rootVChk0 (rs : List (Nat × Nat × Nat)) : Bool :=
  rs.all fun r => (fRootV 0).any fun v => pdEq (pdOf (nfD (B0 ()) (eOf v 0))) (oneK.1, dig3 r.1, 1)

end CFSG.KC.M3BF

end
