module

public import Certificates.Data.Kernel.Fi22Nbr3153

public section

namespace CFSG.KC.S2301

open CFSG.KC.Enum CFSG.KC.N3153

@[expose] noncomputable def bindK (n G B : Nat) : Bool :=
  allN n fun x => Nat.beq (pg (nat_lit 12) (nat_lit 4095) G x) (pg (nat_lit 11) (nat_lit 2047) B x)

@[expose] noncomputable def pM : Nat := nat_lit 4398046511093

@[expose] noncomputable def bM : Nat := nat_lit 1000003

@[expose] noncomputable def xg (X k : Nat) : Nat :=
  fld(X, Nat.mul (nat_lit 48) k, nat_lit 281474976710655)

@[expose] noncomputable def rk (Q v : Nat) : Nat := fld(Q, Nat.mul (nat_lit 11) v, nat_lit 2047)

@[expose] noncomputable def tg (T v : Nat) : Nat := pg (nat_lit 12) (nat_lit 4095) T v

@[expose] noncomputable def vg (H v : Nat) : Nat :=
  fld(H, Nat.mul (nat_lit 64) (Nat.add v (nat_lit 1)), nat_lit 18446744073709551615)

@[expose] noncomputable def tabOK (n K X Q : Nat) : Bool :=
  bAnd(allN (Nat.sub K (nat_lit 1)) (fun k => Nat.blt (xg X k) (xg X (Nat.add k (nat_lit 1)))),
    allN n (fun v => Nat.blt (rk Q v) K))

@[expose] noncomputable def ordOK (n Q O : Nat) : Bool :=
  bAnd(allN n (fun i => Nat.blt (rg O i) n),
  bAnd(allN (Nat.sub n (nat_lit 1)) (fun i => Nat.ble (rk Q (rg O i)) (rk Q (rg O (Nat.add i (nat_lit 1))))),
    Nat.beq (foldN n (fun i a => Nat.lor a (Nat.shiftLeft (nat_lit 1) (rg O i))) (nat_lit 0))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))))

@[expose] noncomputable def injOK (n X Q O : Nat) : Bool :=
  bAnd(allN n (fun i => Nat.blt (rg O i) n),
    allN (Nat.sub n (nat_lit 1)) (fun i =>
      Nat.blt (xg X (rk Q (rg O i))) (xg X (rk Q (rg O (Nat.add i (nat_lit 1)))))))

@[expose] noncomputable def wmaskK (d r : Nat) : Nat :=
  foldN d (fun i a => Nat.add a (Nat.shiftLeft (nat_lit 18446744073709551615)
    (Nat.mul (nat_lit 64) (Nat.add (rg r i) (nat_lit 1))))) (nat_lit 0)

@[expose] noncomputable def maskOK (d : Nat) (R W : Nat → Nat) (x : Nat) : Bool :=
  Nat.beq (Nat.shiftRight (W x) (nat_lit 64)) (Nat.shiftRight (wmaskK d (R x)) (nat_lit 64))

@[expose] noncomputable def onesK (n : Nat) : Nat :=
  foldN (Nat.add n (nat_lit 1)) (fun v a => Nat.add a (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 64) v)))
    (nat_lit 0)

@[expose] noncomputable def redK (L H h : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.land (Nat.shiftRight h (nat_lit 42)) H) (nat_lit 11)) (Nat.land h L)

@[expose] noncomputable def stepW (E L H Wm y h : Nat) : Nat :=
  redK L H (Nat.add h (Nat.land (Nat.add (Nat.mul h (nat_lit 1000002)) (Nat.mul y E)) Wm))

@[expose] noncomputable def startK (X Q T v : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mod (Nat.add (Nat.mul (Nat.mod (Nat.add (xg X (rk Q v)) (nat_lit 7)) pM) bM)
    (Nat.add (xg X (rk Q (tg T v))) (nat_lit 1))) pM) (nat_lit 7)) pM

@[expose] noncomputable def startVec (n X Q T s : Nat) : Nat :=
  foldN n (fun v a => Nat.add a (Nat.shiftLeft (startK X Q T v) (Nat.mul (nat_lit 64) (Nat.add v (nat_lit 1)))))
    s

@[expose] noncomputable def codesK (n X Q T O : Nat) (W : Nat → Nat) : Nat :=
  strictN (onesK n) fun E =>
  strictN (Nat.mul E (nat_lit 4398046511103)) fun L =>
  strictN (Nat.mul E (nat_lit 4194303)) fun H =>
    foldN n (fun i h => strictN (rg O (Nat.sub (Nat.sub n (nat_lit 1)) i)) fun w =>
        stepW E L H (W w) (Nat.add (xg X (rk Q w)) (nat_lit 1)) h)
      (startVec n X Q T (nat_lit 5))

@[expose] noncomputable def roundOK (n X Q X' Q' T O : Nat) (W : Nat → Nat) : Bool :=
  strictB (codesK n X Q T O W) fun C =>
    allN n (fun v => Nat.beq (Nat.mod (vg C v) pM) (xg X' (rk Q' v)))

@[expose] noncomputable def indivOK (X Q X' Q' p j v : Nat) : Bool :=
  Nat.beq (xg X' (rk Q' v)) (nIf(Nat.beq v p, Nat.add pM j, xg X (rk Q v)))

@[expose] noncomputable def initOK (fx : Bool) (X Q : Nat) (M : Nat → Nat) (T v : Nat) : Bool :=
  Nat.beq (xg X (rk Q v)) (Bool.rec (motive := fun _ => Nat)
    (nIf(Nat.beq (Nat.land (Nat.shiftRight (M v) (tg T v)) (nat_lit 1)) (nat_lit 1), nat_lit 1,
      nat_lit 0))
    (nIf(Nat.beq (tg T v) v, nat_lit 1, nat_lit 0)) fx)

@[expose] noncomputable def cellCntK (n Q q : Nat) : Nat :=
  foldN n (fun w a => nIf(Nat.beq (rk Q w) q, Nat.add a (nat_lit 1), a)) (nat_lit 0)

end CFSG.KC.S2301

end
