module

public import Certificates.Data.Kernel.Spor.Row

public section

namespace CFSG.KS.Row

open CFSG.KC.Enum

@[expose] noncomputable def rletter (w m : Nat) (F G O : Nat → Nat) (z : Int) (y : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => rg w m F (O (Nat.sub k (nat_lit 1))) y)
    (fun k => rg w m G (O k) y) z

@[expose] noncomputable def rwordPt (w m : Nat) (F G O : Nat → Nat) (wd : List Int) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (ih x) (fun y => rletter w m F G O z y)) wd

end CFSG.KS.Row

end
