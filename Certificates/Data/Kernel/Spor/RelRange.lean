module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.Ord

@[expose] noncomputable def relsRangeOK (RB : Nat → Nat) (mul : Nat → Nat → Nat)
    (rels : List (List (Nat × Bool))) (L ONE lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB ih (relOK RB mul rels L ONE (Nat.add lo k))) n

end CFSG.KC.Ord

end
