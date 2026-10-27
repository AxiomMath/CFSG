module

public import Certificates.Data.Kernel.A45Cls.Defs

public section

namespace CFSG.KC.A45Cls

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def anyL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ ih => Bool.rec (motive := fun _ => Bool) ih true (f x)) L

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => Bool.rec (motive := fun _ => Bool) false ih (f x)) L

@[expose] noncomputable def allNL (N : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) N

@[expose] noncomputable def nrmInvL (a : Nat) (BL : List Nat) : Bool :=
  allL BL fun b => anyL BL fun c => eq22 45 6 (mask 6) a b c a

@[expose] noncomputable def witL (a : Nat) (BL : List Nat) : Bool :=
  anyL BL fun β => Bool.rec (motive := fun _ => Bool) false
    (Nat.beq (fixK 45 6 (pcomp 45 6 (mask 6) a β)) 15) (eq22 45 6 (mask 6) a β β a)

@[expose] noncomputable def outL (N : Nat) (T : Nat → Nat) (BL : List Nat) : Bool :=
  allNL N fun i => Bool.rec (motive := fun _ => Bool) true (witL (T i) BL) (nrmInvL (T i) BL)

end CFSG.KC.A45Cls

end
