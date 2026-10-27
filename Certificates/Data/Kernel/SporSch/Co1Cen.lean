module

public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KC.Co1B

@[expose] noncomputable def cenPtK (A B X p : Nat) : Bool :=
  bIf(bAnd(eqK (mulWK p A) (mulWK A p), eqK (mulWK p B) (mulWK B p)),
    bIf(allN (nat_lit 5) (fun k => bIf(eqK p (powWK X k), false, true)), false, true), true)

@[expose] noncomputable def cenK (A B X N : Nat) (P : Nat → Nat) : Bool :=
  allN N fun i => strictB (P i) (cenPtK A B X)

end CFSG.KS.SporSch.M24

end
