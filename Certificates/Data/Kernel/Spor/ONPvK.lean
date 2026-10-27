module

public import Certificates.Data.Kernel.Spor.ONNQK

public section

namespace CFSG.KS.ONPv

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONNQ

@[expose] noncomputable def iT (TT UU : Nat → Nat → Nat) (v x : Nat) : Nat :=
  trace TT UU (Nat.shiftRight v (nat_lit 8)) (Nat.land v (nat_lit 255)) x

@[expose] noncomputable def iU (TT UU : Nat → Nat → Nat) (v x : Nat) : Nat :=
  traceR TT UU (Nat.shiftRight v (nat_lit 8)) (Nat.land v (nat_lit 255)) x

@[expose] noncomputable def itT (T U : Nat → Nat → Nat) (D : Nat → Nat) (o k x : Nat) : Nat :=
  iT T U (D (Nat.add o k)) x

@[expose] noncomputable def itU (T U : Nat → Nat → Nat) (D : Nat → Nat) (o k x : Nat) : Nat :=
  iU T U (D (Nat.add o k)) x

@[expose] noncomputable def hT (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itT TT UU D (nat_lit 77) k x

@[expose] noncomputable def hU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itU TT UU D (nat_lit 77) k x

@[expose] noncomputable def qT (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itT (hT TT UU D) (hU TT UU D) D (nat_lit 149) k x

@[expose] noncomputable def qU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itU (hT TT UU D) (hU TT UU D) D (nat_lit 149) k x

@[expose] noncomputable def gsel (k : Nat) : Nat := nIf(Nat.beq k (nat_lit 3), nat_lit 4, k)

@[expose] noncomputable def gT (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  qT TT UU D (gsel k) x

@[expose] noncomputable def gU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  qU TT UU D (gsel k) x

@[expose] noncomputable def c502At (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (p : Nat) : Bool :=
  bAnd(allBlk (nat_lit 178) (fun j => Nat.beq (iT (itT TT UU D (nat_lit 0))
      (itU TT UU D (nat_lit 0)) (D j) p) p) (nat_lit 29),
    bAnd(Nat.beq (iT (itT TT UU D (nat_lit 0)) (itU TT UU D (nat_lit 0)) (D (nat_lit 207)) p)
        (iT TT UU (D (nat_lit 79)) p),
      Nat.beq (iT (itT TT UU D (nat_lit 0)) (itU TT UU D (nat_lit 0)) (D (nat_lit 208)) p)
        (TT (nat_lit 1) p)))

@[expose] noncomputable def c502Hd (TT UU : Nat → Nat → Nat) (D : Nat → Nat) : Bool :=
  strictB (D (nat_lit 19)) fun x =>
    bAnd(Nat.blt x (nat_lit 245520), Bool.not (Nat.beq (iT TT UU (D (nat_lit 79)) x) x))

@[expose] noncomputable def c505At (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (p : Nat) : Bool :=
  allBlk (nat_lit 156) (fun j => Nat.beq (iT (qT TT UU D) (qU TT UU D) (D j) p) p) (nat_lit 19)

@[expose] noncomputable def c505Hd (TT UU : Nat → Nat → Nat) (D : Nat → Nat) : Bool :=
  bAnd(strictB (D (nat_lit 20)) fun x => bAnd(Nat.blt x (nat_lit 245520),
      Bool.not (Nat.beq (qT TT UU D (nat_lit 0) x) x)),
    allBlk (nat_lit 0) (fun k => Nat.beq (qT TT UU D k (nat_lit 0)) (nat_lit 0)) (nat_lit 4))

@[expose] noncomputable def c503At (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (p : Nat) : Bool :=
  bAnd(Nat.beq (iT (gT TT UU D) (gU TT UU D) (D (nat_lit 175)) p) (qT TT UU D (nat_lit 3) p),
    Nat.beq (iT (gT TT UU D) (gU TT UU D) (D (nat_lit 176)) p)
      (iT (gT TT UU D) (gU TT UU D) (D (nat_lit 177)) p))

@[expose] noncomputable def c503Hd (TT UU : Nat → Nat → Nat) (D : Nat → Nat) : Bool :=
  Bool.not (Nat.beq (qT TT UU D (nat_lit 4) (nat_lit 0)) (nat_lit 0))

@[expose] noncomputable def conjAt (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (v k y : Nat) : Nat :=
  strictN (qU TT UU D (Nat.add (nat_lit 5) k) y) fun a =>
    strictN (iT TT UU v a) fun b => qT TT UU D (Nat.add (nat_lit 5) k) b

@[expose] noncomputable def c506At (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (p : Nat) : Bool :=
  strictB (D (nat_lit 92)) fun v =>
    bAnd(allBlk (nat_lit 0) (fun k => Nat.beq (conjAt TT UU D v k p)
        (strictN (iT TT UU v p) fun a => strictN (iT TT UU v a) fun b => iT TT UU v b)) (nat_lit 2),
      allBlk (nat_lit 0) (fun m => Nat.beq (iT TT UU (D (Nat.add (nat_lit 80) m)) p)
        (iT TT UU (D (Nat.add (nat_lit 7) m)) p)) (nat_lit 12))

@[expose] noncomputable def c506Wit (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (j : Nat) : Bool :=
  strictB (D (Nat.add (nat_lit 21) j)) fun w => strictB (Nat.shiftRight w (nat_lit 1)) fun p =>
    strictB (Nat.land w (nat_lit 1)) fun k => strictB (D (Nat.add (nat_lit 93) j)) fun v =>
      bAnd(Nat.blt p (nat_lit 245520),
        Bool.not (Nat.beq (conjAt TT UU D v k (iT TT UU v p)) (iT TT UU v (conjAt TT UU D v k p))))

@[expose] noncomputable def c506WitR (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (lo cnt : Nat) :
    Bool :=
  allBlk lo (c506Wit TT UU D) cnt

@[expose] noncomputable def c506Ln (LT LU : Nat → Nat → Nat) (D : Nat → Nat) (l2 : Nat) : Bool :=
  bAnd(allBlk (nat_lit 7) (fun m => Nat.beq (trV LT LU (nat_lit 0) (D m) (nat_lit 0)) (nat_lit 0))
      (nat_lit 8),
    bAnd(allBlk (nat_lit 7) (fun m => Nat.beq (trV LT LU (nat_lit 1) (D m) l2) l2) (nat_lit 4),
      bAnd(allBlk (nat_lit 15) (fun m => Nat.beq (trV LT LU (nat_lit 1) (D m) l2) l2) (nat_lit 4),
        Nat.beq (iT (itT (actT LT (nat_lit 1)) (actT LU (nat_lit 1)) D (nat_lit 77))
          (itU (actT LT (nat_lit 1)) (actT LU (nat_lit 1)) D (nat_lit 77)) (D (nat_lit 154)) l2) l2)))

end CFSG.KS.ONPv

end
