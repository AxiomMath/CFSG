module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.S63K

open CFSG.KC.Enum

@[expose] noncomputable def orbRowK (W Pa La : Nat → Nat) (k h : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih j c => strictN (W (Nat.add (Nat.mul k h) j)) fun w =>
      nIf(Nat.blt w c, ih (Nat.succ j) c,
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (Pa c) h, Nat.beq (La c) j)),
          ih (Nat.succ j) (Nat.succ c), nat_lit 0)))

@[expose] noncomputable def orbRunK (W Pa La : Nat → Nat) (k : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih h c => nIf(Nat.blt h c,
      strictN (orbRowK W Pa La k h k (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, ih (Nat.succ h) c'), c))

@[expose] noncomputable def orbConsK (N cnt : Nat) (O Ps : Nat → Nat) : Bool :=
  bAnd(allN cnt fun i => bAnd(Nat.blt (O i) N, Nat.beq (Ps (O i)) i),
    allN N fun y => bIf(Nat.beq (Ps y) N, true, bAnd(Nat.blt (Ps y) cnt, Nat.beq (O (Ps y)) y)))

@[expose] noncomputable def layRowK (N : Nat) (QI Lay Par : Nat → Nat) (x : Nat) :
    List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun y _ ih c => strictN (QI y) fun w =>
      nIf(Nat.blt y N, nIf(Nat.blt w c, ih c,
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (Par y) x, Nat.beq (Lay y) (Nat.succ (Lay x)))),
          ih (Nat.succ c), nat_lit 0)), nat_lit 0))

@[expose] noncomputable def layRunK (N : Nat) (Q QI Lay Par : Nat → Nat) (nb : Nat → List Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih h c => nIf(Nat.blt h c,
      strictN (layRowK N QI Lay Par (Q h) (nb (Q h)) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, ih (Nat.succ h) c'), c))

@[expose] noncomputable def layConsK (N : Nat) (Q QI Lay Par : Nat → Nat) : Bool :=
  bAnd(allN N fun i => bAnd(Nat.blt (Q i) N, Nat.beq (QI (Q i)) i),
    bAnd(allN N fun y => bAnd(Nat.blt (QI y) N, bAnd(Nat.beq (Q (QI y)) y, Nat.blt (Lay y) 255)),
      bAnd(Nat.beq (Lay (Q 0)) 0, Nat.beq (Par (Q 0)) 0)))

end CFSG.KC.S63K

end
