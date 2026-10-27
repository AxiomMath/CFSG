module

public import Certificates.Data.Kernel.Fi23K.Defs

public section

namespace CFSG.KC.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23K

@[expose] noncomputable def fixQK (G : Nat → Nat) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => bAnd(Nat.beq (wv G w (nat_lit 0)) (nat_lit 0),
      bAnd(Nat.beq (wv G w (nat_lit 1)) (nat_lit 1), ih))) W

end CFSG.KC.Fi23Nt

end
