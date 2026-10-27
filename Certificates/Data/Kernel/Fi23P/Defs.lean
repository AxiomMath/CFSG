module

public import Certificates.Data.Kernel.Fi23K.Defs

public section

namespace CFSG.KC.Fi23P

open CFSG.KC.Enum CFSG.KC.Fi23K

@[expose] noncomputable def gOK (k : Nat) : Bool :=
  bAnd(Nat.blt k (nat_lit 10), Bool.not (Nat.beq k (nat_lit 8)))

@[expose] noncomputable def nbrOK (T : Nat → Nat → Nat) (lab pos : Nat → Nat) (c ky k y : Nat) :
    Bool :=
  strictB (T k y) fun z =>
    bAnd(Nat.beq (lab z) c, Nat.ble ky (Nat.add (Nat.mul (nat_lit 16) (pos z)) k))

@[expose] noncomputable def nbrsOK (T : Nat → Nat → Nat) (lab pos : Nat → Nat) (c ky y : Nat) :
    Bool :=
  bAnd(nbrOK T lab pos c ky (nat_lit 0) y, bAnd(nbrOK T lab pos c ky (nat_lit 1) y,
  bAnd(nbrOK T lab pos c ky (nat_lit 2) y, bAnd(nbrOK T lab pos c ky (nat_lit 3) y,
  bAnd(nbrOK T lab pos c ky (nat_lit 4) y, bAnd(nbrOK T lab pos c ky (nat_lit 5) y,
  bAnd(nbrOK T lab pos c ky (nat_lit 6) y, bAnd(nbrOK T lab pos c ky (nat_lit 7) y,
    nbrOK T lab pos c ky (nat_lit 9) y))))))))

@[expose] noncomputable def keyOf (gen par pos : Nat → Nat) (x : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 16) (pos (par x))) (gen x)

@[expose] noncomputable def inner (T : Nat → Nat → Nat) (off lab gen par pos pts : Nat → Nat)
    (c P y : Nat) : Bool :=
  strictB (par y) fun q => strictB (gen y) fun g => strictB (pos q) fun pq =>
    bAnd(gOK g, bAnd(Nat.blt q (nat_lit 31671), bAnd(Nat.beq (lab q) c,
    bAnd(Nat.beq (T g q) y, bAnd(Nat.blt pq P,
    strictB (Nat.add (Nat.mul (nat_lit 16) pq) g) fun ky =>
      bAnd(bIf(Nat.blt (Nat.succ (off c)) P, Nat.blt (keyOf gen par pos (pts (Nat.sub P (nat_lit 1)))) ky,
        true), nbrsOK T lab pos c ky y))))))

@[expose] noncomputable def bfsAt (T : Nat → Nat → Nat) (rt off lab gen par pos pts : Nat → Nat)
    (y : Nat) : Bool :=
  bAnd(Nat.beq (pos (pts y)) y, strictB (lab y) fun c => strictB (pos y) fun P =>
    bAnd(Nat.beq (pts P) y, bAnd(Nat.blt c (nat_lit 3), bAnd(Nat.ble (off c) P,
    bAnd(Nat.blt P (off (Nat.succ c)),
    bIf(Nat.beq P (off c),
      bAnd(Nat.beq y (rt c), bAnd(Nat.beq (par y) (nat_lit 0), bAnd(Nat.beq (gen y) (nat_lit 0),
        nbrsOK T lab pos c (nat_lit 0) y))),
      inner T off lab gen par pos pts c P y))))))

@[expose] noncomputable def bfsHd (rt off lab pos : Nat → Nat) : Bool :=
  bAnd(Nat.beq (off (nat_lit 0)) (nat_lit 0), bAnd(Nat.blt (nat_lit 0) (off (nat_lit 1)),
  bAnd(Nat.blt (off (nat_lit 1)) (off (nat_lit 2)), bAnd(Nat.blt (off (nat_lit 2)) (off (nat_lit 3)),
  bAnd(Nat.beq (off (nat_lit 3)) (nat_lit 31671),
    allN (nat_lit 3) fun c => bAnd(Nat.blt (rt c) (nat_lit 31671),
      bAnd(Nat.beq (lab (rt c)) c, Nat.beq (pos (rt c)) (off c))))))))

@[expose] noncomputable def bfsOK (T : Nat → Nat → Nat) (rt off lab gen par pos pts : Nat → Nat) :
    Bool :=
  bAnd(bfsHd rt off lab pos, allN (nat_lit 31671) (bfsAt T rt off lab gen par pos pts))

@[expose] noncomputable def depAt (rt lab par dep : Nat → Nat) (y : Nat) : Bool :=
  strictB (dep y) fun e => bAnd(Nat.blt e (nat_lit 100),
    bIf(Nat.beq y (rt (lab y)), Nat.beq e (nat_lit 0), Nat.beq e (Nat.succ (dep (par y)))))

@[expose] noncomputable def wR (G W : Nat → Nat) (o m x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun i ih x => strictN (tb G (W (Nat.add o i)) x) ih) m x

end CFSG.KC.Fi23P

end
