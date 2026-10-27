module

public import Certificates.Data.Kernel.Fi23C.Defs

public section

namespace CFSG.KC.Fi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23C

@[expose] noncomputable def lJ (G : Nat → Nat) (p x : Nat) : Nat :=
  nIf(Nat.blt p (nat_lit 31671), cJ G p x, tb G (Nat.sub p (nat_lit 31671)) x)

@[expose] noncomputable def wJ (G : Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun p _ ih => lJ G p ih) w

@[expose] noncomputable def memS (H : Nat → Nat) (s c x : Nat) : Bool :=
  Nat.blt (tb H (Nat.succ s) x) c

@[expose] def qL : List Nat :=
  [nat_lit 0, nat_lit 1, nat_lit 32, nat_lit 37, nat_lit 39, nat_lit 49, nat_lit 52, nat_lit 53,
    nat_lit 59, nat_lit 64, nat_lit 71]

@[expose] noncomputable def listK (H : Nat → Nat) (rl rp c bd : Nat) : Bool :=
  bAnd(allN c fun i => strictB (tb H rl i) fun k =>
      bAnd(Nat.blt k bd, Nat.beq (tb H rp k) i),
  bAnd(allN (Nat.pred c) fun i => Nat.blt (tb H rl i) (tb H rl (Nat.succ i)),
    allN bd fun x => strictB (tb H rp x) fun m =>
      bIf(Nat.blt m c, Nat.beq (tb H rl m) x, Nat.beq m c)))

@[expose] noncomputable def presK (G H : Nat → Nat) (s c : Nat) (w : List Nat) : Bool :=
  allN c fun i => memS H s c (wJ G w (tb H s i))

@[expose] noncomputable def qK (G H : Nat → Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => bAnd(memS H (nat_lit 0) (nat_lit 3240) (wJ G w q), ih)) qL

@[expose] noncomputable def cntT (G H : Nat → Nat) (w : List Nat) : Nat :=
  foldN (nat_lit 3240) (fun i a =>
    nIf(memS H (nat_lit 0) (nat_lit 3240) (wJ G w (tb H (nat_lit 0) i)), Nat.succ a, a)) (nat_lit 0)

@[expose] noncomputable def cntK (G H : Nat → Nat) (w : List Nat) (c : Nat) : Bool :=
  Nat.beq (cntT G H w) c

@[expose] noncomputable def trAt (G H : Nat → Nat) (b gr ng : Nat) (dom : Nat → Bool) (s j : Nat) :
    Bool :=
  strictB (tb H b j) fun p => strictB (tb H (Nat.succ b) j) fun r =>
    bAnd(Nat.blt p (nat_lit 31671), bAnd(dom p, bAnd(Nat.beq (tb H (Nat.add b (nat_lit 3)) p) j,
      bIf(Nat.beq j s, Nat.beq r j,
        strictB (tb H (Nat.add b (nat_lit 2)) j) fun l =>
          bAnd(Nat.ble s r, bAnd(Nat.blt r j, bAnd(Nat.blt l ng,
            Nat.beq (cJ G (tb H gr l) (tb H b r)) p)))))))

@[expose] noncomputable def trK (G H : Nat → Nat) (b gr ng : Nat) (dom : Nat → Bool)
    (s lo c : Nat) : Bool :=
  allN c fun i => trAt G H b gr ng dom s (Nat.add lo i)

@[expose] noncomputable def covK (H : Nat → Nat) (b n : Nat) (dom : Nat → Bool) : Bool :=
  allN (nat_lit 31671) fun x => bIf(dom x,
    strictB (tb H (Nat.add b (nat_lit 3)) x) fun m => bAnd(Nat.blt m n, Nat.beq (tb H b m) x), true)

@[expose] noncomputable def ctAt (G H : Nat → Nat) (b j : Nat) : Bool :=
  strictB (tb H b j) fun p => strictB (tb H (Nat.succ b) j) fun r =>
    bAnd(Nat.blt p (nat_lit 31671), bAnd(memS H (nat_lit 2) (nat_lit 1080) p,
      bAnd(Nat.beq (tb H (Nat.add b (nat_lit 3)) p) j,
        bIf(Nat.beq j (nat_lit 0), Nat.beq r (nat_lit 0),
          bAnd(Nat.blt r j, Nat.beq (cJ G (tb H b r) p) p)))))

@[expose] noncomputable def ctK (G H : Nat → Nat) (b lo c : Nat) : Bool :=
  allN c fun i => ctAt G H b (Nat.add lo i)

@[expose] noncomputable def starK (G H HC : Nat → Nat) (fc c0 c1 : Nat) : Bool :=
  allN (nat_lit 3510) fun u => strictB (tb HC (nat_lit 0) (tb HC (nat_lit 3) u)) fun x =>
    bAnd(Bool.rec (motive := fun _ => Bool) (Bool.not (memS H (nat_lit 4) c0 u))
        (memS H (nat_lit 4) c0 u) (memS H (nat_lit 2) (nat_lit 1080) x),
      Bool.rec (motive := fun _ => Bool) (Bool.not (Nat.beq (cJ G fc x) x))
        (Nat.beq (cJ G fc x) x) (memS H (nat_lit 6) c1 u))

@[expose] noncomputable def domT (H : Nat → Nat) (x : Nat) : Bool := memS H (nat_lit 0) (nat_lit 3240) x

@[expose] noncomputable def domTc (H : Nat → Nat) (x : Nat) : Bool :=
  Bool.not (memS H (nat_lit 0) (nat_lit 3240) x)

@[expose] noncomputable def domO (H : Nat → Nat) (x : Nat) : Bool := memS H (nat_lit 2) (nat_lit 1080) x

@[expose] noncomputable def domR (H : Nat → Nat) (x : Nat) : Bool :=
  bAnd(memS H (nat_lit 0) (nat_lit 3240) x, Bool.not (memS H (nat_lit 2) (nat_lit 1080) x))

@[expose] noncomputable def domW (G H : Nat → Nat) (w : List Nat) (x : Nat) : Bool :=
  Bool.not (memS H (nat_lit 0) (nat_lit 3240) (wJ G w x))

@[expose] noncomputable def genK (G H : Nat → Nat) (gr n : Nat) (fx : Bool) (f : Nat)
    (w : List Nat) : Bool :=
  allN n fun i => strictB (tb H gr i) fun y =>
    bAnd(memS H (nat_lit 0) (nat_lit 3240) y,
      bIf(fx, Nat.beq (cJ G y f) f, memS H (nat_lit 0) (nat_lit 3240) (wJ G w y)))

end CFSG.KC.Fi23T

end
