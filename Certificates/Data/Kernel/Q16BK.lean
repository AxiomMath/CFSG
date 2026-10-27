module

public import Certificates.Data.Kernel.BfsPinBase

public section

namespace CFSG.KC.Q16BK

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def wptK (w : Nat) (L : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun c _ acc => pg w (mask w) c acc) L

@[expose] noncomputable def keyWK (n w : Nat) (ps L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ acc => Nat.add (wptK w L x) (Nat.mul n acc)) ps

@[expose] noncomputable def ptQ (n w : Nat) (ps : List Nat) (N : Nat) (T : Nat → Nat) (nR : Nat)
    (RI C W : Nat → Nat) (e i : Nat) : Bool :=
  strictB (T i) fun x =>
    bIf(Nat.beq (keyWK n w ps [x, x, x, x]) e, true,
      bIf(Nat.beq (keyWK n w ps [x, x, x, x, x, x, x, x]) e,
        strictB (C i) fun c => strictB (W i) fun j =>
          bAnd(Nat.blt c nR, bAnd(Nat.blt j N, strictB (T j) fun g =>
            Nat.beq (keyWK n w ps [g, x]) (keyWK n w ps [T (RI c), g]))),
        true))

@[expose] noncomputable def repQ (n w : Nat) (ps : List Nat) (N : Nat) (T : Nat → Nat) (r : Nat) :
    Bool :=
  strictB (keyWK n w ps [r, r, r, r]) fun k4 =>
    allN N fun j => strictB (T j) fun y =>
      bIf(Nat.beq (keyWK n w ps [y, y]) k4,
        bIf(Nat.beq (keyWK n w ps [r, y, r]) (keyWK n w ps [y]), false, true), true)

@[expose] noncomputable def q16BK (n w : Nat) (ps : List Nat) (N : Nat) (T : Nat → Nat) (nR : Nat)
    (RI C W : Nat → Nat) : Bool :=
  strictB (keyWK n w ps []) fun e =>
    bAnd(allN N (ptQ n w ps N T nR RI C W e),
      allN nR fun c => bAnd(Nat.blt (RI c) N, repQ n w ps N T (T (RI c))))

end CFSG.KC.Q16BK

end
