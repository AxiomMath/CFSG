module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.Fi24F4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Mathieu

@[expose] noncomputable def letP (S SI : Nat → Nat) (z : Int) : Nat :=
  strictN (icode z) (fun c => nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
    S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1))))

@[expose] noncomputable def wPt (w m : Nat) (S SI : Nat → Nat) (wd : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun z _ ih => strictN ih (fun y => pg w m (letP S SI z) y)) wd

@[expose] noncomputable def recOK (n w m : Nat) (P : Nat) (S SI : Nat → Nat) (wd : List Int) : Bool :=
  bAnd(canonK n w m (Nat.mul n w) P, allN n (fun x => Nat.beq (pg w m P x) (wPt w m S SI wd x)))

@[expose] noncomputable def cntComm (n w m : Nat) (T : Nat → Nat) (Y lo len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun d ih => strictN ih (fun c =>
    strictN (T (Nat.add lo d)) (fun t =>
      nIf(Nat.beq (pcomp n w m t Y) (pcomp n w m Y t), Nat.succ c, c)))) len

end CFSG.KC.Fi24F4

end
