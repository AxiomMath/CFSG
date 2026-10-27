module

public import Certificates.Data.Kernel.M24G.Kzero

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G CFSG.KC.ONanSmall

@[expose] def fuseInvF (S : List (Array Nat)) (pA pB : KTree (Nat × Nat)) : Bool :=
  S.all fun t => kzeroKeyF (mulTabF t t) != kzeroKeyF Native.kzeroId ||
    kzeroKeyF t == kzeroKeyF Native.kzeroId || (findK (kzeroKeyF t) pA).isSome ||
    (findK (kzeroKeyF t) pB).isSome

end CFSG.KC.M24G
