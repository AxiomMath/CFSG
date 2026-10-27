module

public import Certificates.Data.Kernel.O8.QuatO8

public section

namespace CFSG.KC.O8

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def lets8K (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a _ ih => bAnd(Nat.blt (nat_lit 0) a, bAnd(Nat.blt a (nat_lit 9), ih))) w

@[expose] noncomputable def rowsLetK (E : List (List Nat × (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => bAnd(Prod.rec (motive := fun _ => Bool) (fun w _ => lets8K w) r, ih)) E

end CFSG.KC.O8

end
