module

public import Certificates.Data.Kernel.SporSch.Co1Mat

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def commK (M : Nat → Nat) (T : Nat) (bidx : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun j _ ih => bAnd(Nat.beq (mulK (M (Nat.sub j (nat_lit 1))) T)
      (mulK T (M (Nat.sub j (nat_lit 1)))), ih)) bidx

@[expose] noncomputable def bindFromK (M M' : Nat → Nat) (bidx : List Nat) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun j _ ih i => bAnd(Nat.beq (M' i) (M (Nat.sub j (nat_lit 1))), ih (Nat.succ i))) bidx k

@[expose] noncomputable def bindK (M M' : Nat → Nat) (bidx : List Nat) : Bool :=
  bindFromK M M' bidx (nat_lit 0)

end CFSG.KS.SporSch.M24

end
