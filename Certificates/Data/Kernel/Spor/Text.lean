module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.Text

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def hexV (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 48), nat_lit 16, nIf(Nat.blt c (nat_lit 58), Nat.sub c (nat_lit 48),
    nIf(Nat.blt c (nat_lit 65), nat_lit 16, nIf(Nat.blt c (nat_lit 71), Nat.sub c (nat_lit 55),
      nat_lit 16))))

@[expose] noncomputable def run (wd n w lines start cnt : Nat) (F : Nat → Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun L e t _ _ => bAnd(Nat.beq L lines, bAnd(Nat.beq e (nat_lit 0), Nat.beq t (nat_lit 0))))
    (fun ch _ ih L e t v acc => strictB (Char.toNat ch) (fun c =>
      bIf(Nat.blt e n,
        strictB (hexV c) (fun h => bIf(Nat.blt h (nat_lit 16),
          strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
          bIf(Nat.beq (Nat.succ t) wd,
            bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
              strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
                ih L (Nat.succ e) (nat_lit 0) (nat_lit 0) acc'),
              false),
            ih L e (Nat.succ t) v' acc)),
          false)),
        bIf(Nat.beq c (nat_lit 10),
          bAnd(bIf(Nat.ble start L, bIf(Nat.blt L (Nat.add start cnt),
              Nat.beq acc (F (Nat.sub L start)), true), true),
            ih (Nat.succ L) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)),
          false))))
    cs

@[expose] noncomputable def hexBind (cs : List Char) (wd n w lines start cnt : Nat) (F : Nat → Nat) :
    Bool :=
  bAnd(Nat.blt (nat_lit 0) wd, bAnd(Nat.ble (Nat.add start cnt) lines,
    run wd n w lines start cnt F cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)))

end CFSG.KS.Text

end
