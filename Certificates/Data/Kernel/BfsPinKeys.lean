module

public import Certificates.Data.Kernel.BfsPin

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def pkeyK (n w : Nat) (ps : List Nat) (P : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ acc => Nat.add (pg w (mask w) P p) (Nat.mul n acc)) ps

@[expose] noncomputable def keysK (n w : Nat) (ps : List Nat) (N : Nat) (T : Nat → Nat) : Bool :=
  allN N fun i => strictB (pkeyK n w ps (T i)) fun ki =>
    allN i fun j => Bool.rec (motive := fun _ => Bool) true false (Nat.beq ki (pkeyK n w ps (T j)))

end CFSG.KC.BfsPin

end
