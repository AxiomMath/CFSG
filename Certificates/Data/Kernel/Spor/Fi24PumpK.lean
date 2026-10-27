module

public import Certificates.Data.Kernel.Spor.Fi24Base
public import Certificates.Data.Kernel.Spor.Fi24FixP

public section

namespace CFSG.KC.Fi24PumpK

open CFSG.KC.Fi24FixP

@[expose] noncomputable def repW (w : List Nat) (p : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun _ ih => w ++ ih) p

@[expose] noncomputable def letLt (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => Nat.blt l (nat_lit 26) && ih) w

@[expose] noncomputable def pairOK (E : List Nat → List Nat → Bool) (A : Nat → Nat → Nat)
    (r v : List Nat) (p n : Nat) : Bool :=
  letLt r && letLt v && E (repW v p) [] && !E v [] && E (r ++ v) (v ++ r) && fixOK A v n

end CFSG.KC.Fi24PumpK

end
