module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.G24Key

open CFSG.KC.Enum

@[expose] noncomputable def tw (w m : Nat) (T : Nat → Nat) (i : Nat) : Nat :=
  strictN (Nat.shiftRight i (nat_lit 6)) (fun b =>
    fld(T b, Nat.mul w (Nat.land i (nat_lit 63)), m))

@[expose] noncomputable def t12 (T : Nat → Nat) (i : Nat) : Nat :=
  tw (nat_lit 12) (nat_lit 4095) T i

@[expose] noncomputable def ap (P p : Nat) : Nat := pg (nat_lit 11) (nat_lit 2047) P p

@[expose] noncomputable def upK (SI PAR PG : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih node p => nIf(Nat.beq node (nat_lit 0), p,
      strictN (Nat.sub node (nat_lit 1)) (fun k =>
        strictN (ap (SI (t12 PG k)) p) (fun q => strictN (t12 PAR k) (fun r => ih r q)))))
    fuel

@[expose] noncomputable def downK (S PAR PG : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih node p => nIf(Nat.beq node (nat_lit 0), p,
      strictN (Nat.sub node (nat_lit 1)) (fun k =>
        strictN (t12 PAR k) (fun r => ap (S (t12 PG k)) (ih r p)))))
    fuel

@[expose] noncomputable def eK (S SI PAR PG : Nat → Nat) (fuel E node p : Nat) : Nat :=
  strictN (upK SI PAR PG fuel node p) (fun q => downK S PAR PG fuel node (ap E q))

@[expose] noncomputable def keyOf (f : Nat → Nat) : Nat :=
  strictN (f (nat_lit 0)) (fun a => strictN (f (nat_lit 1)) (fun b => strictN (f (nat_lit 2))
    (fun c => Nat.add (Nat.mul (Nat.add (Nat.mul a (nat_lit 2048)) b) (nat_lit 2048)) c)))

@[expose] noncomputable def keyK (S SI PAR PG : Nat → Nat) (fuel E node : Nat) : Nat :=
  keyOf (eK S SI PAR PG fuel E node)

@[expose] noncomputable def walkK (PAR : Nat → Nat) (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun node => node)
    (fun _ ih node => nIf(Nat.beq node (nat_lit 0), nat_lit 0,
      strictN (t12 PAR (Nat.sub node (nat_lit 1))) ih))
    fuel

@[expose] noncomputable def rootK (PAR : Nat → Nat) (fuel n : Nat) : Bool :=
  allN n (fun k => Nat.beq (walkK PAR fuel k) (nat_lit 0))

@[expose] noncomputable def sortedK (K ORD : Nat → Nat) (n : Nat) : Bool :=
  Nat.blt (nat_lit 0) (foldN n (fun i s => nIf(Nat.beq s (nat_lit 0), nat_lit 0,
    strictN (t12 ORD i) (fun o => nIf(Nat.blt o n,
      strictN (K o) (fun k => nIf(Nat.blt (Nat.succ k) s, Nat.succ k, nat_lit 0)), nat_lit 0))))
    (nat_lit 8589934593))

@[expose] noncomputable def kpt (k t : Nat) : Nat :=
  fld(k, Nat.mul (nat_lit 11) (Nat.sub (nat_lit 2) t), nat_lit 2047)

@[expose] noncomputable def kmap (g k : Nat) : Nat := keyOf (fun t => ap g (kpt k t))

@[expose] noncomputable def treeK (S TP TG : Nat → Nat) (fuel : Nat) (K : Nat → Nat) (n : Nat) :
    Bool :=
  allN n (fun k => Nat.beq (K k) (keyOf (downK S TP TG fuel k)))

@[expose] noncomputable def closK (G : Nat → Nat) (J : Nat) (K CL : Nat → Nat) (n : Nat) : Bool :=
  allN n (fun i => strictB (K i) (fun ki => allN J (fun j =>
    strictB (t12 CL (Nat.add (Nat.mul J i) j)) (fun c =>
      bAnd(Nat.blt c n, Nat.beq (K c) (kmap (G j) ki))))))

@[expose] noncomputable def wpt (A B W L p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p
    (fun i ih => ap (nIf(Nat.beq fld(W, i, nat_lit 1) (nat_lit 0), A, B)) ih) L

@[expose] noncomputable def recK (S TP TG : Nat → Nat) (fuel : Nat) (K : Nat → Nat)
    (A B R0 R1 k r : Nat) : Bool :=
  strictB (K k) (fun ky =>
  bIf(Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 0),
    strictB (Nat.shiftRight r (nat_lit 1)) (fun b => bAnd(Nat.blt b (nat_lit 3),
      bIf(Nat.beq k (nat_lit 0), true,
        bIf(Nat.beq (downK S TP TG fuel k (kpt ky b)) b, false, true)))),
    bAnd(bIf(Nat.beq k (nat_lit 0), false, true),
      strictB fld(r, nat_lit 2, nat_lit 255) (fun L =>
      strictB (Nat.shiftRight r (nat_lit 10)) (fun W =>
      allN (nat_lit 3) (fun b => strictB (kpt ky b) (fun eb =>
        bAnd(Nat.beq (downK S TP TG fuel k eb) b,
          Nat.beq (wpt A B W L eb)
            (ap (nIf(Nat.beq fld(r, nat_lit 1, nat_lit 1) (nat_lit 0), R0, R1))
              (wpt A B W L b))))))))))

@[expose] noncomputable def commB (a b : Nat) : Bool :=
  allN (nat_lit 3) (fun t => Nat.beq (ap a (ap b t)) (ap b (ap a t)))

end CFSG.KC.G24Key

end
