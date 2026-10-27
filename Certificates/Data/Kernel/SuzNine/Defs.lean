module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.SuzNine

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def fldK (k t : Nat) : Nat :=
  Nat.land (Nat.shiftRight k (Nat.mul (nat_lit 11) t)) (nat_lit 2047)

@[expose] noncomputable def actK (k g : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => Nat.lor acc (Nat.shiftLeft (fldK g (fldK k t)) (Nat.mul (nat_lit 11) t)))
    (nat_lit 30)

@[expose] noncomputable def idKey : Nat :=
  nat_lit 966941685120183595472605568907850244617238437574676992076999419801145191590412349758109857645332480

@[expose] noncomputable def segK (k j : Nat) : Nat :=
  Nat.land (Nat.shiftRight k (Nat.mul (nat_lit 66) j)) (nat_lit 73786976294838206463)

@[expose] noncomputable def centAt (E CT : Nat → Nat) (k : Nat) : Bool :=
  allN (nat_lit 4) fun j =>
    Nat.beq (segK (E k) (Nat.succ j)) (segK (E (CT (Nat.add (Nat.mul k (nat_lit 4)) j))) (nat_lit 0))

@[expose] noncomputable def cenOK (E CT : Nat → Nat) (iz k : Nat) : Bool :=
  impB (centAt E CT k) (orB (Nat.beq k (nat_lit 0)) (Nat.beq k iz))

@[expose] def UW : List (List Int) := [[2, 6, 2], [2, 9, 2, 9], [4, 7, 4, 9], [6, 9, 8, 5]]

end CFSG.KC.SuzNine

end
