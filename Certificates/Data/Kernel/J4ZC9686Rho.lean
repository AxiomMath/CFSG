module

public import Certificates.Data.Kernel.J4M2Hex
public import Certificates.Data.CFSGNative.J4ZCent.Check

public section

namespace CFSG.KC.J4ZC9686

open CFSG.KC.Enum CFSG.KC.LQT.L CFSG.KS.PK CFSG.KC.J4M2K
open CFSG.Sporadic.J4.ZCent (g0W rW tW)

@[expose] noncomputable def codeL (l : List Nat) : Nat :=
  pmk (nat_lit 77) (nat_lit 7) fun i => l.getD i 0

@[expose] noncomputable def sigW (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (one7 (nat_lit 77))
    (fun l _ ih => mul7 (nat_lit 77) (sigC (Nat.sub (Int.toNat l) 1)) ih) w

@[expose] noncomputable def b0C (i : Nat) : Nat := sigW (g0W.getD i [])

@[expose] noncomputable def i3C : Nat :=
  mul7 (nat_lit 77) (b0C 3) (mul7 (nat_lit 77) (b0C 3) (b0C 3))

@[expose] noncomputable def i4C : Nat := mul7 (nat_lit 77) (b0C 4) (b0C 4)

@[expose] noncomputable def letC (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => b0C (Nat.sub n 1))
    (fun n => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (one7 (nat_lit 77)) i4C (Nat.beq n 4)) i3C (Nat.beq n 3))
    l

@[expose] noncomputable def wordC (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (one7 (nat_lit 77))
    (fun l _ ih => mul7 (nat_lit 77) (letC l) ih) w

@[expose] def negOK (w : List Int) : Bool := w.all fun l => decide (0 < l) || l == -4 || l == -5

@[expose] noncomputable def rhoCore (S R : SetK) (P : List Nat) (A B : Nat) : Bool :=
  bAnd(closedK7 (nat_lit 77) [A, B] S, bAnd(Nat.beq S.size (nat_lit 960),
    bAnd(allR (nat_lit 16) fun i => memT S.t (b0C i),
    bAnd(Nat.beq A (ev7 ((List.range 16).map b0C) [4, 4, 13]),
    bAnd(Nat.beq B (ev7 ((List.range 16).map b0C) [15, 4, 4, 12]),
    bAnd(Nat.beq (mul7 (nat_lit 77) (b0C 3) i3C) (one7 (nat_lit 77)),
    bAnd(Nat.beq (mul7 (nat_lit 77) (b0C 4) i4C) (one7 (nat_lit 77)),
    bAnd(closedK7 (nat_lit 77) P R,
      allR (nat_lit 60) fun i => bIf(Nat.beq i 0, true,
        bIf(memT R.t (wordC (tW.getD i [])), false, true))))))))))

@[expose] noncomputable def rhoChk (L0 L1 : List Nat) : Bool :=
  strictB (codeL L0) fun A => strictB (codeL L1) fun B =>
    rhoCore (bfsK7 (nat_lit 77) [A, B] (nat_lit 64)) (bfsK7 (nat_lit 77) (rW.map wordC) (nat_lit 64))
      (rW.map wordC) A B

end CFSG.KC.J4ZC9686
