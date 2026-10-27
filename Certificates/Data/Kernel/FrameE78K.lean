module

public import Certificates.Data.Kernel.OrbRow.Defs

public section

namespace CFSG.KC.FrameE78

open CFSG.KC.Enum CFSG.KC.OrbRow

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def ln (x q : Nat) : Nat := fld(x, Nat.mul (nat_lit 2) q, nat_lit 3)

@[expose] noncomputable def cij (C p j : Nat) : Nat :=
  fld(C, Nat.mul (nat_lit 2) (Nat.add (Nat.mul (nat_lit 8) p) j), nat_lit 3)

@[expose] noncomputable def vget (V i : Nat) : Nat := fld(V, Nat.mul (nat_lit 16) i, nat_lit 65535)

@[expose] noncomputable def bitB (M i : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land M (Nat.shiftLeft (nat_lit 1) i))

@[expose] noncomputable def sV (n C j x : Nat) : Nat :=
  strictN (ln x j) fun xj =>
    nIf(Nat.beq xj (nat_lit 0), x,
      Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun p ih => Nat.lor ih (Nat.shiftLeft
          (Nat.mod (Nat.add (ln x p) (Nat.mul (nat_lit 2) (Nat.mul xj (cij C p j)))) (nat_lit 3))
          (Nat.mul (nat_lit 2) p))) n)

@[expose] noncomputable def negL (x : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (Nat.land x (nat_lit 21845)) (nat_lit 1))
    (Nat.shiftRight (Nat.land x (nat_lit 43690)) (nat_lit 1))

@[expose] noncomputable def lead (n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih y => strictN (Nat.land y (nat_lit 3)) fun a =>
      nIf(Nat.beq a (nat_lit 0), ih (Nat.shiftRight y (nat_lit 2)), a)) n x

@[expose] noncomputable def normV (n x : Nat) : Nat :=
  nIf(Nat.beq (lead n x) (nat_lit 2), negL x, x)

@[expose] noncomputable def validV (n x : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight x (Nat.mul (nat_lit 2) n)) (nat_lit 0),
    Nat.beq (Nat.land (Nat.land x (Nat.shiftRight x (nat_lit 1))) (nat_lit 21845)) (nat_lit 0))

@[expose] noncomputable def dot3 (n u v : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q ih => Nat.add ih (Nat.mul (ln u q) (ln v q))) n) (nat_lit 3)

@[expose] noncomputable def cvec (n C c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p ih => Nat.lor ih (Nat.shiftLeft
      (Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun q ih' => Nat.add ih' (Nat.mul (cij C p q) (ln c q))) n) (nat_lit 3))
      (Nat.mul (nat_lit 2) p))) n

@[expose] noncomputable def sRt (c Cc i : Nat) : Nat :=
  Nat.lor (Nat.sub c (Nat.shiftLeft (ln c i) (Nat.mul (nat_lit 2) i)))
    (Nat.shiftLeft (Nat.mod (Nat.add (ln c i) (Nat.mul (nat_lit 2) (ln Cc i))) (nat_lit 3))
      (Nat.mul (nat_lit 2) i))

@[expose] noncomputable def rget (RP a : Nat) : Nat :=
  fld(RP, Nat.mul (nat_lit 32) a, nat_lit 4294967295)

@[expose] noncomputable def rc (RP a : Nat) : Nat := Nat.land (rget RP a) (nat_lit 65535)

@[expose] noncomputable def rC (RP a : Nat) : Nat := Nat.shiftRight (rget RP a) (nat_lit 16)

@[expose] noncomputable def bf (n RP a b : Nat) : Nat := dot3 n (rc RP a) (rC RP b)

@[expose] noncomputable def ptsOK (n N V : Nat) : Bool :=
  bAnd(Nat.beq (Nat.mul (nat_lit 2) N) (Nat.sub (Nat.pow (nat_lit 3) n) (nat_lit 1)),
    allN N fun i => strictB (vget V i) fun v =>
      bAnd(validV n v, bAnd(Nat.beq (lead n v) (nat_lit 1),
        bIf(Nat.blt (Nat.succ i) N, Nat.blt v (vget V (Nat.succ i)), true))))

@[expose] noncomputable def genJ (n C N : Nat) (S : List Nat) (V j : Nat) : Bool :=
  strictB (getS S j) fun s => allN N fun q => strictB (pg (nat_lit 12) (nat_lit 4095) s q) fun r =>
    bAnd(Nat.blt r N, Nat.beq (vget V r) (normV n (sV n C j (vget V q))))

@[expose] noncomputable def rootOK (n C m RP : Nat) : Bool :=
  allN m fun a => strictB (rc RP a) fun c =>
    bAnd(validV n c, bAnd(Nat.beq (rget RP a) (Nat.lor c (Nat.shiftLeft (cvec n C c) (nat_lit 16))),
      Nat.beq (dot3 n c (cvec n C c)) (nat_lit 2)))

@[expose] noncomputable def simpleOK (n RP : Nat) : Bool :=
  allN n fun i => Nat.beq (rc RP i) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 2) i))

@[expose] noncomputable def clget (CL a i : Nat) : Nat :=
  fld(CL, Nat.add (Nat.mul (nat_lit 64) a) (Nat.mul (nat_lit 8) i), nat_lit 255)

@[expose] noncomputable def closOK (n m RP CL : Nat) : Bool :=
  allN m fun a => allN n fun i => strictB (clget CL a i) fun b =>
    strictB (sRt (rc RP a) (rC RP a) i) fun d =>
      bAnd(Nat.blt b m, orB (Nat.beq d (rc RP b)) (Nat.beq d (negL (rc RP b))))

@[expose] noncomputable def parOK (n m CL PT : Nat) : Bool :=
  allN (Nat.sub m n) fun a' => strictB (Nat.add n a') fun a => strictB (vget PT a) fun f =>
    strictB (Nat.land f (nat_lit 255)) fun p => strictB (Nat.shiftRight f (nat_lit 8)) fun i =>
      bAnd(Nat.blt p a, bAnd(Nat.blt i n, Nat.beq (clget CL p i) a))

@[expose] noncomputable def distOK (m RP : Nat) : Bool :=
  allN m fun a => strictB (rc RP a) fun c => allN a fun b => strictB (rc RP b) fun e =>
    bAnd(notB (Nat.beq c e), notB (Nat.beq c (negL e)))

@[expose] noncomputable def coverOK (N k : Nat) (D : List Nat) : Bool :=
  allN N fun p => notB (allN k fun t => Nat.beq (depD (getS D t) p) (nat_lit 255))

@[expose] noncomputable def cntN (m : Nat) (f : Nat → Bool) : Nat :=
  foldN m (fun i s => nIf(f i, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def txOK (n m RP x Tm : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight Tm m) (nat_lit 0),
    allN m fun a => bIf(Nat.beq (dot3 n (rc RP a) x) (nat_lit 0), bitB Tm a, notB (bitB Tm a)))

@[expose] noncomputable def unifK (n m RP Tm t d : Nat) : Bool :=
  bAnd(Nat.beq (cntN m (bitB Tm)) t,
    allN m fun a => bIf(bitB Tm a,
      Nat.beq (cntN m fun b => bAnd(bitB Tm b, bAnd(notB (Nat.beq b a),
        notB (Nat.beq (bf n RP a b) (nat_lit 0))))) d, true))

@[expose] noncomputable def alwK (n t d : Nat) : Bool :=
  orB (bAnd(Nat.beq n (nat_lit 7), orB (bAnd(Nat.beq t (nat_lit 21), Nat.beq d (nat_lit 10)))
      (orB (bAnd(Nat.beq t (nat_lit 30), Nat.beq d (nat_lit 16)))
        (bAnd(Nat.beq t (nat_lit 36), Nat.beq d (nat_lit 20))))))
    (bAnd(Nat.beq n (nat_lit 8), orB (bAnd(Nat.beq t (nat_lit 36), Nat.beq d (nat_lit 14)))
      (orB (bAnd(Nat.beq t (nat_lit 42), Nat.beq d (nat_lit 20)))
        (bAnd(Nat.beq t (nat_lit 63), Nat.beq d (nat_lit 32))))))

@[expose] noncomputable def splitK (n m RP Tm P : Nat) : Bool :=
  bAnd(Nat.beq (Nat.land P Tm) P, bAnd(notB (Nat.beq P (nat_lit 0)),
    bAnd(notB (Nat.beq P Tm), strictB (Nat.xor Tm P) fun Q =>
      allN m fun a => bIf(bitB P a,
        allN m fun b => bIf(bitB Q b, Nat.beq (bf n RP a b) (nat_lit 0), true), true))))

@[expose] noncomputable def repK (n m RP V b : Nat) (Q : List Nat) : Bool :=
  strictB (vget V b) fun x => strictB (getS Q (nat_lit 0)) fun Tm =>
    strictB (getS Q (nat_lit 1)) fun kd => strictB (getS Q (nat_lit 2)) fun t =>
      bAnd(txOK n m RP x Tm,
        bIf(Nat.beq kd (nat_lit 0),
          strictB (getS Q (nat_lit 3)) fun d => bAnd(alwK n t d, unifK n m RP Tm t d),
          bAnd(Nat.beq kd (nat_lit 1), splitK n m RP Tm t)))

end CFSG.KC.FrameE78

end
