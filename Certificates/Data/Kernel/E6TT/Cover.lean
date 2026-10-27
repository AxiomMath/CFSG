module

public import Certificates.Data.E6TableT
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictN strictB)
open Certificates.Data.E6TableT (Vec reps genAct)

@[expose] noncomputable def enc : Vec → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.add (Int.toNat x) (Nat.mul (nat_lit 3) ih))

@[expose] noncomputable def dg (c p : Nat) : Int := Int.ofNat (Nat.mod (Nat.div c p) (nat_lit 3))

@[expose] noncomputable def dec (c : Nat) : Vec :=
  [dg c (nat_lit 1), dg c (nat_lit 3), dg c (nat_lit 9), dg c (nat_lit 27), dg c (nat_lit 81),
    dg c (nat_lit 243)]

@[expose] noncomputable def bitN (s c : Nat) : Bool :=
  Nat.beq fld(s, c, nat_lit 1) (nat_lit 1)

@[expose] noncomputable def coverStep (e seen : Nat) : Nat :=
  strictN (Nat.land e (nat_lit 1023)) fun c =>
  strictN (Nat.shiftRight e (nat_lit 20)) fun j =>
    nIf(bIf(Nat.ble (nat_lit 7) j,
        Nat.beq c (enc (reps.getD (Nat.sub j (nat_lit 7)) [])),
        strictB fld(e, nat_lit 10, nat_lit 1023) fun p =>
          bAnd(bitN seen p, Nat.beq c (enc (genAct j (dec p))))),
      Nat.lor seen (Nat.shiftLeft (nat_lit 1) c),
      Nat.lor seen (nat_lit 1))

@[expose] noncomputable def coverRun : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun seen => seen)
    (fun e _ ih seen => strictN (coverStep e seen) ih)

@[expose] noncomputable def coverK (CT : List Nat) : Bool :=
  Nat.beq (coverRun CT (nat_lit 0)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 729)) (nat_lit 2))

end CFSG.KC.E6TT

end
