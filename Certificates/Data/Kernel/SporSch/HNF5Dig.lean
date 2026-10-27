module

public import Certificates.Data.Kernel.SporSch.HNF5

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def digRun5 (x : Nat) (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (nat_lit 133))
    (fun ch _ ih j => strictB (Char.toNat ch) (fun c => bAnd(Nat.ble (nat_lit 48) c,
      bAnd(Nat.beq (Nat.sub c (nat_lit 48)) (lane5 x j), ih (Nat.succ j))))) cs

@[expose] noncomputable def dig5K (x : Nat) (cs : List Char) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight x (nat_lit 2128)) (nat_lit 0), digRun5 x cs (nat_lit 0))

end CFSG.KS.SporSch

end
