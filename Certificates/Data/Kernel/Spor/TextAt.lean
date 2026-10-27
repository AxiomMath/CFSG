module

public import Certificates.Data.Kernel.Spor.Text

public section

namespace CFSG.KS.Text

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def asciiK (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ch _ ih => bAnd(Nat.blt (Char.toNat ch) (nat_lit 128), ih)) cs

@[expose] noncomputable def lineRun (wd n w P : Nat) (ds : List Char) :
    Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun e _ _ acc => bAnd(Nat.beq e n, Nat.beq acc P))
    (fun ch _ ih e t v acc => bIf(Nat.blt e n,
      strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
        strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) wd,
          bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
            strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
              ih (Nat.succ e) (nat_lit 0) (nat_lit 0) acc'),
            false),
          ih e (Nat.succ t) v' acc)),
        false)),
      Nat.beq acc P))
    ds

@[expose] noncomputable def lineK (wd n w P : Nat) (ds : List Char) : Bool :=
  bAnd(Nat.blt (nat_lit 0) wd, lineRun wd n w P ds (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0))

end CFSG.KS.Text

end
