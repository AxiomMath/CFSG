module

public import Certificates.Data.Kernel.Spor.ONK

public section

namespace CFSG.KS.ONNQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def twH (b h : Nat) : Nat :=
  nIf(Nat.beq b (nat_lit 0), h, nIf(Nat.beq h (nat_lit 0), nat_lit 5,
    nIf(Nat.beq h (nat_lit 2), nat_lit 6, nIf(Nat.beq h (nat_lit 3), nat_lit 7, h))))

@[expose] noncomputable def actT (TT : Nat → Nat → Nat) (b h i : Nat) : Nat := TT (twH b h) i

@[expose] noncomputable def traceR (TT UU : Nat → Nat → Nat) (W L x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun k ih v => strictN (fld(W, Nat.mul (nat_lit 4) k, nat_lit 15)) fun c =>
      strictN (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), UU (Nat.shiftRight c (nat_lit 1)) v,
        TT (Nat.shiftRight c (nat_lit 1)) v)) ih) L x

@[expose] noncomputable def trV (TT UU : Nat → Nat → Nat) (b v x : Nat) : Nat :=
  trace (actT TT b) (actT UU b) (Nat.shiftRight v (nat_lit 8)) (Nat.land v (nat_lit 255)) x

@[expose] noncomputable def trVR (TT UU : Nat → Nat → Nat) (b v x : Nat) : Nat :=
  traceR (actT TT b) (actT UU b) (Nat.shiftRight v (nat_lit 8)) (Nat.land v (nat_lit 255)) x

@[expose] noncomputable def fstAt (TT UU : Nat → Nat → Nat) (D FR : Nat → Nat) (n y : Nat) : Bool :=
  strictB (FR y) fun r => strictB (Nat.shiftRight r (nat_lit 21)) fun l =>
    strictB (fld(r, nat_lit 17, nat_lit 15)) fun d =>
      bIf(Nat.beq d (nat_lit 0),
        bAnd(Nat.blt l (nat_lit 36), strictB (D l) fun v => Nat.beq (trV TT UU (nat_lit 0) v (nat_lit 0)) y),
        bAnd(Nat.blt l (nat_lit 4), strictB (Nat.land r (nat_lit 131071)) fun p => bAnd(Nat.blt p n,
          bAnd(Nat.blt (fld(FR p, nat_lit 17, nat_lit 15)) d,
            strictB (D (Nat.add (nat_lit 36) l)) fun v => Nat.beq (trV TT UU (nat_lit 0) v p) y))))

@[expose] noncomputable def fstRange (TT UU : Nat → Nat → Nat) (D FR : Nat → Nat) (n lo cnt : Nat) :
    Bool :=
  allBlk lo (fstAt TT UU D FR n) cnt

@[expose] noncomputable def cosAt (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (l2 i : Nat) : Bool :=
  strictB (D (Nat.add (nat_lit 16456) i)) fun t =>
    bAnd(strictB (D (Nat.add (nat_lit 40) i)) fun v => Nat.beq (trV TT UU (nat_lit 1) v l2) t,
      allBlk (nat_lit 0) (fun q =>
        strictB (D (Nat.add (nat_lit 16912) (Nat.add (Nat.mul (nat_lit 4) i) q))) fun j =>
          bAnd(Nat.blt j (nat_lit 456), strictB (D (Nat.add (nat_lit 18736) q)) fun v =>
            Nat.beq (trV TT UU (nat_lit 1) v t) (D (Nat.add (nat_lit 16456) j)))) (nat_lit 4))

@[expose] noncomputable def cosRange (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (l2 lo cnt : Nat) :
    Bool :=
  allBlk lo (cosAt TT UU D l2) cnt

@[expose] noncomputable def wLet (TT UU : Nat → Nat → Nat) (N : Nat → Nat) (gv mv b c x : Nat) :
    Nat :=
  strictN (Nat.shiftRight c (nat_lit 1)) fun k =>
    nIf(Nat.blt k (nat_lit 4),
      nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), trV TT UU b (N k) x, trVR TT UU b (N k) x),
      nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        strictN (trV TT UU b mv x) fun z => trV TT UU b gv z,
        strictN (trVR TT UU b gv x) fun z => trVR TT UU b mv z))

@[expose] noncomputable def wTr (TT UU : Nat → Nat → Nat) (N : Nat → Nat) (gv mv b W L x : Nat) :
    Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
    (fun _ ih k v => strictN (fld(W, Nat.mul (nat_lit 4) k, nat_lit 15)) fun c =>
      strictN (wLet TT UU N gv mv b c v) fun v' => ih (Nat.succ k) v') L (nat_lit 0) x

@[expose] noncomputable def nSel (n0 n1 n2 n3 k : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), n0, nIf(Nat.beq k (nat_lit 1), n1, nIf(Nat.beq k (nat_lit 2), n2, n3)))

@[expose] noncomputable def witAt (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (l2 j : Nat) : Bool :=
  strictB (D (Nat.succ (Nat.div j (nat_lit 456)))) fun gv =>
    strictB (D (Nat.add (nat_lit 40) (Nat.mod j (nat_lit 456)))) fun mv =>
    strictB (D (nat_lit 36)) fun n0 => strictB (D (nat_lit 37)) fun n1 =>
    strictB (D (nat_lit 38)) fun n2 => strictB (D (nat_lit 39)) fun n3 =>
    strictB (D (Nat.add (nat_lit 496) j)) fun v =>
      strictB (Nat.shiftRight v (nat_lit 8)) fun W => strictB (Nat.land v (nat_lit 255)) fun L =>
        strictB (wTr TT UU (nSel n0 n1 n2 n3) gv mv (nat_lit 0) W L (nat_lit 0)) fun x =>
          strictB (wTr TT UU (nSel n0 n1 n2 n3) gv mv (nat_lit 1) W L l2) fun y =>
            bIf(Nat.beq x (nat_lit 0), Bool.not (Nat.beq y l2), Nat.beq y l2)

@[expose] noncomputable def witRange (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (l2 lo cnt : Nat) :
    Bool :=
  allBlk lo (witAt TT UU D l2) cnt

@[expose] noncomputable def headOK (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (l2 : Nat) : Bool :=
  bAnd(Nat.beq (trV TT UU (nat_lit 0) (D (nat_lit 18740)) (nat_lit 0)) l2,
    bAnd(Nat.beq (trV TT UU (nat_lit 0) (D (nat_lit 0)) (nat_lit 0)) (nat_lit 0),
      bAnd(allBlk (nat_lit 0) (fun k =>
          Nat.beq (trV TT UU (nat_lit 1) (D (Nat.add (nat_lit 36) k)) l2) l2) (nat_lit 4),
        bAnd(Nat.beq (trV TT UU (nat_lit 1) (D (nat_lit 40)) l2) l2,
          Bool.not (Nat.beq (trV TT UU (nat_lit 1) (D (nat_lit 41)) l2) l2)))))

end CFSG.KS.ONNQ

end
