module

public import Certificates.Data.Kernel.WeylE8.D8

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def frameKey (k : Nat) : Nat :=
  strictN (Nat.mul (nat_lit 2) (Nat.shiftRight k (nat_lit 1))) fun a =>
    Bool.rec (motive := fun _ => Nat)
      (Nat.add (Nat.add (Nat.mul (nat_lit 2) REP) (Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) a)))
        (Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) (Nat.succ a))))
      (Nat.sub (Nat.add (Nat.mul (nat_lit 2) REP) (Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) a)))
        (Nat.shiftLeft (nat_lit 2) (Nat.mul (nat_lit 4) (Nat.succ a))))
      (Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0))

@[expose] noncomputable def frameRootsOK (RK : Nat → Nat) (FR : Nat) : Bool :=
  allN (nat_lit 8) fun k => strictB (pg (nat_lit 8) (nat_lit 255) FR k) fun e =>
    bAnd(Nat.blt e (nat_lit 240), Nat.beq (RK e) (frameKey k))

@[expose] noncomputable def frameImg (RK : Nat → Nat) (FR a x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => strictN (Nat.sub (nat_lit 7) j) fun k =>
      ih (nIf(Nat.beq (Nat.land (Nat.shiftRight a k) (nat_lit 1)) (nat_lit 1),
        reflKey x (RK (pg (nat_lit 8) (nat_lit 255) FR k)), x)))
    (nat_lit 8) x

@[expose] noncomputable def frameRowOK (RK : Nat → Nat) (FR a T : Nat) : Bool :=
  allN (nat_lit 240) fun i => strictB (pg (nat_lit 8) (nat_lit 255) T i) fun e =>
    bAnd(Nat.blt e (nat_lit 240), Nat.beq (RK e) (frameImg RK FR a (RK i)))

@[expose] noncomputable def low (X : Nat) : Nat := Nat.land X (mask (nat_lit 1920))

@[expose] noncomputable def commT (T : Nat → Nat) (g : Nat → Nat) (n : Nat) : Bool :=
  allN n fun j => strictB (T (g j)) fun A => allN j fun k => strictB (T (g k)) fun B =>
    Nat.beq (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) A B)
      (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) B A)

@[expose] noncomputable def homF (FT : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 8) (fun t => strictB (Nat.shiftLeft (nat_lit 1) t) fun m => strictB (FT m) fun G =>
    allN m fun b => Nat.beq (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) (FT b) G) (low (FT (Nat.add b m)))),
    commT FT (fun t => Nat.shiftLeft (nat_lit 1) t) (nat_lit 8))

@[expose] noncomputable def homS (ST : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 7) (fun k => strictB (Nat.shiftLeft (nat_lit 2) k) fun m =>
    strictB (ST (Nat.add (nat_lit 1) m)) fun G => allN m fun b => bIf(evenB b,
      Nat.beq (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) (ST b) G)
        (low (ST (Nat.xor b (Nat.add (nat_lit 1) m)))), true)),
    commT ST (fun k => Nat.add (nat_lit 1) (Nat.shiftLeft (nat_lit 2) k)) (nat_lit 7))

@[expose] noncomputable def distK (T : Nat → Nat) (p : Nat → Bool) : Bool :=
  allN (nat_lit 256) fun a => bIf(p a, strictB (low (T a)) fun A => allN a fun b =>
    bIf(p b, notB' (Nat.beq A (low (T b))), true), true)

@[expose] noncomputable def factAt (LR TRI : Nat → Nat) (BP : Nat) (T sg : Nat) : Bool :=
  bAnd(permOK (nat_lit 240) (nat_lit 8) (nat_lit 255) (nat_lit 1920) T T,
    bAnd(Nat.beq (Nat.shiftRight T (nat_lit 1920)) (nat_lit 0),
      bAnd(siftK (nat_lit 240) (nat_lit 8) (mask (nat_lit 8)) (nat_lit 1920) (pidn (nat_lit 240) (nat_lit 8))
          LR TRI BP (nat_lit 8) (nat_lit 0) T,
        Nat.beq (Nat.land (Nat.div (Nat.sub (nat_lit 240) (fixCntK (nat_lit 240) (nat_lit 8) T)) (nat_lit 2))
          (nat_lit 1)) sg)))

@[expose] noncomputable def factsF (FT LR TRI : Nat → Nat) (BP : Nat) : Bool :=
  allN (nat_lit 256) fun a => factAt LR TRI BP (FT a) (Nat.land (pop8 a) (nat_lit 1))

@[expose] noncomputable def factsS (ST LR TRI : Nat → Nat) (BP : Nat) : Bool :=
  allN (nat_lit 256) fun a => bIf(evenB a, factAt LR TRI BP (ST a) (nat_lit 0), true)

@[expose] noncomputable def linksOK (RT ST FT PT : Nat → Nat) (NEG KP : Nat) : Bool :=
  bAnd(allN (nat_lit 8) (fun i => Nat.beq (FT (Nat.shiftLeft (nat_lit 1) i))
      (RT (pg (nat_lit 8) (nat_lit 255) KP i))),
  bAnd(Nat.beq (FT (nat_lit 255)) NEG, bAnd(Nat.beq (ST (nat_lit 255)) NEG,
  bAnd(allN (nat_lit 4) (fun j => strictB (Nat.mul (nat_lit 3) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 2) j)))
      fun m => Nat.beq (ST m) (FT m)),
    Nat.beq (PT (nat_lit 0)) (RT (nat_lit 1))))))

end CFSG.KLC.E8

end
