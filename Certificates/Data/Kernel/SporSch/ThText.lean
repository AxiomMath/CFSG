module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def decV (c : Nat) : Nat :=
  nIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)), Nat.sub c (nat_lit 48), nat_lit 16)

@[expose] noncomputable def hexV2 (c : Nat) : Nat :=
  nIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)), Nat.sub c (nat_lit 48),
  nIf(bAnd(Nat.ble (nat_lit 97) c, Nat.ble c (nat_lit 102)), Nat.sub c (nat_lit 87),
  nIf(bAnd(Nat.ble (nat_lit 65) c, Nat.ble c (nat_lit 70)), Nat.sub c (nat_lit 55), nat_lit 16)))

@[expose] noncomputable def wordEnd (B v pos acc cnt bad found : Nat) (k : Nat → Nat → Nat → Nat) :
    Nat :=
  nIf(Nat.beq pos (nat_lit 0), k cnt bad found,
    k (Nat.succ cnt) (nIf(Nat.blt acc B, bad, nat_lit 1)) (nIf(Nat.beq acc v, nat_lit 1, found)))

@[expose] noncomputable def thScanRun (hex : Bool) (B v : Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat)
    (fun pos acc cnt bad found => wordEnd B v pos acc cnt bad found (fun cnt bad found =>
      Nat.add (Nat.mul (nat_lit 4) cnt) (Nat.add (Nat.mul (nat_lit 2) found) bad)))
    (fun ch _ ih pos acc cnt bad found => strictN (Char.toNat ch) (fun c =>
      nIf(bIf(Nat.beq c (nat_lit 32), true, Nat.beq c (nat_lit 10)),
        wordEnd B v pos acc cnt bad found (fun cnt bad found =>
          strictN cnt (fun cnt => ih (nat_lit 0) (nat_lit 0) cnt bad found)),
        nIf(bAnd(hex, bAnd(Nat.beq c (nat_lit 120), bAnd(Nat.beq pos (nat_lit 1), Nat.beq acc (nat_lit 0)))),
          ih (nat_lit 2) acc cnt bad found,
          strictN (Bool.rec (motive := fun _ => Nat) (decV c) (hexV2 c) hex) (fun d =>
            nIf(Nat.blt d (Bool.rec (motive := fun _ => Nat) (nat_lit 10) (nat_lit 16) hex),
              strictN (Nat.add (Nat.mul (Bool.rec (motive := fun _ => Nat) (nat_lit 10) (nat_lit 16) hex)
                acc) d) (fun acc' => strictN (Nat.succ pos) (fun pos' => ih pos' acc' cnt bad found)),
              ih (nat_lit 1) acc cnt (nat_lit 1) found))))))
    cs

@[expose] noncomputable def thScanK (hex : Bool) (B v : Nat) (cs : List Char) : Nat :=
  thScanRun hex B v cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def thBindRun (hex : Bool) (R : Nat → Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
    (fun pos acc cnt bad => nIf(Nat.beq pos (nat_lit 0),
      Nat.add (Nat.mul (nat_lit 2) cnt) bad,
      Nat.add (Nat.mul (nat_lit 2) (Nat.succ cnt)) (nIf(Nat.beq acc (R cnt), bad, nat_lit 1))))
    (fun ch _ ih pos acc cnt bad => strictN (Char.toNat ch) (fun c =>
      nIf(bIf(Nat.beq c (nat_lit 32), true, Nat.beq c (nat_lit 10)),
        nIf(Nat.beq pos (nat_lit 0), ih (nat_lit 0) (nat_lit 0) cnt bad,
          strictN (Nat.succ cnt) (fun cnt' =>
            ih (nat_lit 0) (nat_lit 0) cnt' (nIf(Nat.beq acc (R cnt), bad, nat_lit 1)))),
        nIf(bAnd(hex, bAnd(Nat.beq c (nat_lit 120), bAnd(Nat.beq pos (nat_lit 1), Nat.beq acc (nat_lit 0)))),
          ih (nat_lit 2) acc cnt bad,
          strictN (Bool.rec (motive := fun _ => Nat) (decV c) (hexV2 c) hex) (fun d =>
            nIf(Nat.blt d (Bool.rec (motive := fun _ => Nat) (nat_lit 10) (nat_lit 16) hex),
              strictN (Nat.add (Nat.mul (Bool.rec (motive := fun _ => Nat) (nat_lit 10) (nat_lit 16) hex)
                acc) d) (fun acc' => strictN (Nat.succ pos) (fun pos' => ih pos' acc' cnt bad)),
              ih (nat_lit 1) acc cnt (nat_lit 1)))))))
    cs

@[expose] noncomputable def thBindK (hex : Bool) (R : Nat → Nat) (cs : List Char) : Nat :=
  thBindRun hex R cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

end CFSG.KS.SporSch

end
