module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.DigitScan

open CFSG.KC.Enum

@[expose] noncomputable def scanRun (F : Nat → Nat → Bool) (N : Nat) (cs : List Char) :
    Nat → Nat → Bool → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool → Bool)
    (fun i v op => bAnd(op, bAnd(F i v, Nat.beq (Nat.succ i) N)))
    (fun ch rest ih i v op => strictB (Char.toNat ch) (fun c =>
      bIf(Nat.beq c (nat_lit 32),
        bAnd(op, bAnd(F i v, strictB (Nat.succ i) (fun j => ih j (nat_lit 0) false))),
      bIf(Nat.beq c (nat_lit 10),
        bAnd(op, bAnd(F i v, bAnd(Nat.beq (Nat.succ i) N,
          List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rest))),
      bAnd(Nat.ble (nat_lit 48) c, bAnd(Nat.ble c (nat_lit 57),
        strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48)))
          (fun u => ih i u true)))))))
    cs

@[expose] noncomputable def scanK (F : Nat → Nat → Bool) (N : Nat) (cs : List Char) : Bool :=
  scanRun F N cs (nat_lit 0) (nat_lit 0) false

end CFSG.KC.DigitScan

end
