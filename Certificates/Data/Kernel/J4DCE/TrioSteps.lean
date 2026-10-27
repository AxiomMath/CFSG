module

public import Certificates.Data.Kernel.M24G.Steps
public import Certificates.Data.CFSGNative.J4DCE.Trio

public section

namespace CFSG.KC.J4DCE

@[expose] def j4StepsF : List (Nat × Nat × Nat → Nat × Nat × Nat) :=
  [CFSG.KC.M24G.imgTrioF CFSG.J4DCE.Native.xTab.toList,
    CFSG.KC.M24G.imgTrioF CFSG.J4DCE.Native.yTab.toList]

@[expose] def j4Base : Nat × Nat × Nat := (2474320, 4207270, 10095625)

end CFSG.KC.J4DCE
