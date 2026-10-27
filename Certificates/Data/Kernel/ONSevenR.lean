module

public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.ONR

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def ent (w G i : Nat) : Nat := pg w (mask w) G i

@[expose] noncomputable def resK (N w : Nat) (T F : Nat → Nat) (G : Nat) : Bool :=
  allN N fun i => strictB (ent w G i) fun j => bAnd(Nat.blt j N, Nat.beq (T j) (F (T i)))

@[expose] noncomputable def orbPtK (N w k : Nat) (T G D : Nat → Nat) (i : Nat) : Bool :=
  bAnd(Nat.blt (T i) (nat_lit 245520),
  bAnd(bIf(Nat.blt i (nat_lit 3), true, strictB (D i) fun d =>
      bAnd(Nat.blt (Nat.div d k) i, bAnd(Nat.beq (ent w (G (Nat.mod d k)) (Nat.div d k)) i,
        bIf(Nat.blt (Nat.succ i) N, Nat.blt d (D (Nat.succ i)), true)))),
    allN k fun j => strictB (ent w (G j) i) fun q =>
      bAnd(Nat.blt q N, bIf(Nat.blt q (nat_lit 3), true, Nat.ble (D q) (Nat.add (Nat.mul k i) j)))))

@[expose] noncomputable def orbK (N w k : Nat) (T G D S : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) k, bAnd(Nat.ble (nat_lit 3) N, bAnd(Nat.ble N (nat_lit 245520),
  bAnd(Nat.beq (T (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (T (nat_lit 1)) (nat_lit 227759),
  bAnd(Nat.beq (T (nat_lit 2)) (nat_lit 100817), bAnd(distinctK N T S,
    allN N (orbPtK N w k T G D))))))))

@[expose] noncomputable def powsK (N w X : Nat) (P : Nat → Nat) (o : Nat) : Bool :=
  bAnd(permB N w X, bAnd(Nat.beq (P (nat_lit 0)) (pidn N w),
    allN o fun e => Nat.beq (P (Nat.succ e)) (pcomp N w (mask w) X (P e))))

@[expose] noncomputable def qK (N w : Nat) (T PL : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 57) (fun j => powsK N w (PL (Nat.add (Nat.mul (nat_lit 8) j) (nat_lit 1)))
      (fun e => PL (Nat.add (Nat.mul (nat_lit 8) j) e)) (nat_lit 7)),
  bAnd(allN (nat_lit 343) (fun k => Nat.beq (ppow N w (mask w) (pidn N w) (T k) (nat_lit 7))
      (pidn N w)),
  bAnd(allN (nat_lit 343) (fun k => bIf(Nat.beq (T k) (pidn N w), true,
      CFSG.KC.LQT.P.anyN (nat_lit 57) fun j => CFSG.KC.LQT.P.anyN (nat_lit 7) fun e =>
        Nat.beq (T k) (PL (Nat.add (Nat.mul (nat_lit 8) j) e)))),
  bAnd(allN (nat_lit 57) (fun j => allN (nat_lit 57) fun j' => bIf(Nat.beq j j', true,
      allN (nat_lit 7) fun e => !(Nat.beq (PL (Nat.add (Nat.mul (nat_lit 8) j) (nat_lit 1)))
        (PL (Nat.add (Nat.mul (nat_lit 8) j') e))))),
    allN (nat_lit 57) (fun j => bAnd(Nat.beq (PL (Nat.add (Nat.mul (nat_lit 8) j) (nat_lit 7)))
        (pidn N w),
      bAnd(!(Nat.beq (PL (Nat.add (Nat.mul (nat_lit 8) j) (nat_lit 1))) (pidn N w)),
        memK (nat_lit 343) T (PL (Nat.add (Nat.mul (nat_lit 8) j) (nat_lit 1))))))))))

@[expose] noncomputable def fK (n nC nF w ng nfg : Nat) (TC TF G FG PX : Nat → Nat) : Bool :=
  bAnd(allN nfg (fun l => memK nC TC (FG l)),
  bAnd(allN ng (fun k => allN nfg fun l =>
      memK nF TF (pcomp n w (mask w) (G k) (pcomp n w (mask w) (FG l)
        (pinvS n w (mask w) (G k))))),
  bAnd(memK nF TF (PX 1),
    allN nC (fun k => bIf(allN nfg fun l => Nat.beq (pcomp n w (mask w) (TC k) (FG l))
        (pcomp n w (mask w) (FG l) (TC k)),
      CFSG.KC.LQT.P.anyN (nat_lit 7) fun e => Nat.beq (TC k) (PX e), true)))))

end CFSG.KC.ONR

end
