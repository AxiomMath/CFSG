module

public import Certificates.Data.Kernel.SporSch.J4STok

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum

@[expose] noncomputable def natOf (w : Nat) (x : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun v => v) (fun _ => Nat.shiftLeft (nat_lit 1) w) x

@[expose] noncomputable def permsK (w n k : Nat) (L : List Int) (T : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun j c _ => bAnd(Nat.beq j k, Nat.beq c (nat_lit 0)))
    (fun x _ ih j c acc => bIf(Nat.beq j k, true,
      strictB (natOf w x) (fun v => bAnd(Nat.blt v (Nat.shiftLeft (nat_lit 1) w),
        strictB (Nat.lor acc (Nat.shiftLeft v (Nat.mul w c))) (fun acc' =>
          bIf(Nat.beq (Nat.succ c) n,
            bAnd(Nat.beq acc' (T j), ih (Nat.succ j) (nat_lit 0) (nat_lit 0)),
            ih j (Nat.succ c) acc'))))))
    L (nat_lit 0) (nat_lit 0) (nat_lit 0)

end CFSG.KS.SporSch.C11

end
