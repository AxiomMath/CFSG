module

public import Certificates.Data.Kernel.WeylE8.TList

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum

@[expose] noncomputable def rootDKey (DP r : Nat) : Nat :=
  strictN (Nat.shiftRight r (nat_lit 2)) fun p => strictN (pa DP p) fun a => strictN (pb DP p) fun b =>
    strictN (Nat.land r (nat_lit 3)) fun s =>
      Nat.sub (Nat.add (Nat.add (Nat.mul (nat_lit 2) REP)
          (nIf(Nat.blt s (nat_lit 2), Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) a), nat_lit 0)))
          (nIf(bIf(Nat.beq s (nat_lit 0), true, Nat.beq s (nat_lit 2)),
            Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) b), nat_lit 0)))
        (Nat.add (nIf(Nat.blt s (nat_lit 2), nat_lit 0, Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) a)))
          (nIf(bIf(Nat.beq s (nat_lit 0), true, Nat.beq s (nat_lit 2)), nat_lit 0,
            Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) b))))

@[expose] noncomputable def rootsDK (RK : Nat → Nat) (DP : Nat) : Bool :=
  allN (nat_lit 112) fun r => Nat.beq (RK r) (rootDKey DP r)

@[expose] noncomputable def signC (m : Nat) : Nat := Nat.add (Nat.shiftLeft m (nat_lit 24)) spId

@[expose] noncomputable def spInvK (c : Nat) : Nat :=
  strictN (sumN (nat_lit 8) fun k => Nat.shiftLeft k (Nat.mul (nat_lit 3) (spAt c k))) fun p =>
    Nat.add p (Nat.shiftLeft (spImgMask p (spMask c)) (nat_lit 24))

@[expose] noncomputable def stabB (x g : Nat) : Bool :=
  strictB (spMul (spMul g x) g) fun c => bIf(Nat.beq c x, true, Nat.beq c (spMul x negC))

@[expose] noncomputable def uniqueAt (GC x : Nat) : Bool :=
  bIf(bAnd(Nat.beq (spMul x x) spId, bAnd(notB' (Nat.beq x spId), bAnd(notB' (Nat.beq x negC),
      bAnd(allN (nat_lit 13) (fun k => stabB x (e32 GC k)), stabB x s0C)))),
    bIf(Nat.beq x (signC (nat_lit 15)), true, Nat.beq x (signC (nat_lit 240))), true)

@[expose] noncomputable def commB (x g : Nat) : Bool := Nat.beq (spMul x g) (spMul g x)

@[expose] noncomputable def centerCAt (GC CG x : Nat) : Bool :=
  bIf(bAnd(commB x (signC (nat_lit 15)), bAnd(allN (nat_lit 7) (fun k => commB x (e32 GC k)),
      allN (nat_lit 6) (fun k => commB x (e32 CG k)))),
    bIf(Nat.beq x spId, true, bIf(Nat.beq x (signC (nat_lit 15)), true,
      bIf(Nat.beq x (signC (nat_lit 240)), true, Nat.beq x negC))), true)

@[expose] noncomputable def cfB (x xi d : Nat) : Bool := frameK' (spMul (spMul (spMul x d) xi) d)

@[expose] noncomputable def centerModAt (GC CG x : Nat) : Bool :=
  strictB (spInvK x) fun xi =>
  bAnd(okC xi, bAnd(Nat.beq (spMul x xi) spId,
    bIf(bAnd(commB x (signC (nat_lit 15)),
        bAnd(allN (nat_lit 7) (fun k => cfB x xi (e32 GC k)),
          allN (nat_lit 6) (fun k => cfB x xi (e32 CG k)))),
      strictB (spMul x (signC (nat_lit 5))) fun a =>
      bIf(frameK' x, true, bIf(frameK' a, true, bIf(frameK' (spMul x (signC (nat_lit 80))), true,
        frameK' (spMul a (signC (nat_lit 80)))))), true)))

@[expose] noncomputable def uAt (PP GC CG i : Nat) : Bool :=
  strictB (tcK PP i) fun t => strictB (spMul t s0C) fun ts =>
    bAnd(uniqueAt GC t, bAnd(uniqueAt GC ts, bAnd(centerCAt GC CG t, bAnd(centerCAt GC CG ts,
      bAnd(centerModAt GC CG t, centerModAt GC CG ts)))))

@[expose] noncomputable def frameCodeK (DP FR v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) spId (fun k ih => strictN ih fun A =>
    nIf(Nat.beq (Nat.land (Nat.shiftRight v k) (nat_lit 1)) (nat_lit 1),
      spMul (reflCodeK DP (pg (nat_lit 8) (nat_lit 255) FR k)) A, A)) (nat_lit 8)

@[expose] noncomputable def fsC (DP FR S v : Nat) : Nat :=
  strictN (frameCodeK DP FR v) fun F => spMul (spMul (spMul F S) F) S

@[expose] noncomputable def hitK (DP FR S w : Nat) : Bool :=
  bAnd(evenB w, notB' (allN (nat_lit 256) fun v => notB' (Nat.beq (fsC DP FR S v) (signC w))))

@[expose] noncomputable def inWK (W n c : Nat) : Bool :=
  notB' (allN n fun j => notB' (Nat.beq c (signC (pg (nat_lit 8) (nat_lit 255) W j))))

@[expose] noncomputable def commSetK (DP FR S W n : Nat) : Bool :=
  bAnd(allN n (fun j => hitK DP FR S (pg (nat_lit 8) (nat_lit 255) W j)),
    allN (nat_lit 256) fun v => inWK W n (fsC DP FR S v))

@[expose] noncomputable def framesOK (DP FR : Nat) : Bool :=
  bAnd(allN (nat_lit 8) (fun k => Nat.blt (pg (nat_lit 8) (nat_lit 255) FR k) (nat_lit 112)),
    allN (nat_lit 256) fun v => okC (frameCodeK DP FR v))

end CFSG.KLC.E8

end
