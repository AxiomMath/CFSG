module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.CentSrch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def wAt (W l : Nat) : Nat := fld(W, Nat.mul (nat_lit 16) l, nat_lit 65535)

@[expose] noncomputable def invW (w m : Nat) (TRI : Nat → Nat) (W i : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun l ih a => strictN (ih a) fun b => pg w m (TRI (wAt W l)) b) i

@[expose] noncomputable def fwdW (w m : Nat) (TR : Nat → Nat) (W i : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun l ih p => strictN (pg w m (TR (wAt W l)) p) ih) i

@[expose] noncomputable def emode (E : Nat) : Nat := Nat.land E (nat_lit 3)
@[expose] noncomputable def eL (E : Nat) : Nat := fld(E, nat_lit 2, nat_lit 7)
@[expose] noncomputable def eJ (E : Nat) : Nat := fld(E, nat_lit 5, nat_lit 7)
@[expose] noncomputable def eNR (E : Nat) : Nat := fld(E, nat_lit 8, nat_lit 255)
@[expose] noncomputable def eRel (E r : Nat) : Nat :=
  fld(E, Nat.add (nat_lit 16) (Nat.mul (nat_lit 8) r), nat_lit 255)
@[expose] noncomputable def eM (E : Nat) : Nat := Nat.shiftRight E (nat_lit 256)

@[expose] noncomputable def dAt (n w m DP j p : Nat) : Nat := pg w m DP (Nat.add (Nat.mul n j) p)

@[expose] noncomputable def imgAt (w m B i a l : Nat) : Nat := nIf(Nat.blt l i, pg w m B l, a)

@[expose] noncomputable def relOK (n w m DP E i B a : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r ih => bAnd(Nat.beq (dAt n w m DP (fld(eRel E r, nat_lit 3, nat_lit 7))
      (imgAt w m B i a (Nat.land (eRel E r) (nat_lit 7)))) a, ih)) (eNR E)

@[expose] noncomputable def leafOK (w m nb : Nat) (TR : Nat → Nat) (BP W B : Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun X _ ih => bAnd(allN nb fun t => Nat.beq (fwdW w m TR W nb (pg w m X (pg w m BP t)))
      (pg w m X (pg w m B t)), ih))

@[expose] noncomputable def child (n w m nw : Nat) (DP E i R W B a k : Nat)
    (ih : Nat → Nat → Nat → Nat) : Nat :=
  nIf(bAnd(Nat.blt k (rcnt R), relOK n w m DP E i B a),
    ih (Nat.succ i) (Nat.lor W (Nat.shiftLeft (Nat.add (roff n nw R) k) (Nat.mul (nat_lit 16) i)))
      (Nat.lor B (Nat.shiftLeft a (Nat.mul w i))),
    nat_lit 0)

@[expose] noncomputable def tgt (n w m nw : Nat) (TRI : Nat → Nat) (DP E i R W B a : Nat)
    (ih : Nat → Nat → Nat → Nat) : Nat :=
  strictN (rpos w m nw R (invW w m TRI W i a)) fun k => child n w m nw DP E i R W B a k ih

@[expose] noncomputable def level (n w m nw : Nat) (TR TRI : Nat → Nat) (DP E i R W B : Nat)
    (ih : Nat → Nat → Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (strictN (dAt n w m DP (eJ E) (pg w m B (eL E))) fun a => tgt n w m nw TRI DP E i R W B a ih)
    (fun e _ => Nat.rec (motive := fun _ => Nat)
      (foldN n (fun p s => nIf(Nat.blt (nat_lit 0) (Nat.land (eM E) (Nat.shiftLeft (nat_lit 1) p)),
        Nat.add s (tgt n w m nw TRI DP E i R W B p ih), s)) (nat_lit 0))
      (fun _ _ => foldN (rcnt R) (fun k s => Nat.add s
        (strictN (fwdW w m TR W i (rpt w m R k)) fun a => child n w m nw DP E i R W B a k ih))
        (nat_lit 0)) e)
    (emode E)

@[expose] noncomputable def relsOK (n w m BP DP E i : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r ih => bAnd(bAnd(Nat.ble (Nat.land (eRel E r) (nat_lit 7)) i,
      Nat.beq (dAt n w m DP (fld(eRel E r, nat_lit 3, nat_lit 7))
        (pg w m BP (Nat.land (eRel E r) (nat_lit 7)))) (pg w m BP i)), ih)) (eNR E)

@[expose] noncomputable def fixAll (n w m DP E i p : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r ih => bAnd(!(Nat.beq (Nat.land (eRel E r) (nat_lit 7)) i) ||
      Nat.beq (dAt n w m DP (fld(eRel E r, nat_lit 3, nat_lit 7)) p) p, ih)) (eNR E)

@[expose] noncomputable def entryOK (n w m BP DP E i : Nat) : Bool :=
  bAnd(relsOK n w m BP DP E i,
    Nat.rec (motive := fun _ => Bool)
      (bAnd(Nat.blt (eL E) i,
        Nat.beq (dAt n w m DP (eJ E) (pg w m BP (eL E))) (pg w m BP i)))
      (fun e _ => Nat.rec (motive := fun _ => Bool)
        (allN n fun p => !(fixAll n w m DP E i p) ||
          Nat.blt (nat_lit 0) (Nat.land (eM E) (Nat.shiftLeft (nat_lit 1) p)))
        (fun e' _ => Nat.beq e' (nat_lit 0)) e)
      (emode E))

@[expose] noncomputable def planOK (n w nb BP DP : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i nb)
    (fun E _ ih i => bAnd(entryOK n w (mask w) BP DP E i, ih (Nat.succ i)))

@[expose] noncomputable def dOK (n w X Y DP : Nat) : Bool :=
  bAnd(bAnd(Nat.beq (ppow n w (mask w) (pidn n w) X (nat_lit 3)) (pidn n w),
    Nat.beq (ppow n w (mask w) (pidn n w) Y (nat_lit 3)) (pidn n w)),
  bAnd(Nat.beq (pcomp n w (mask w) X Y) (pcomp n w (mask w) Y X),
    allN (nat_lit 8) fun j => Nat.beq (fld(DP, Nat.mul (Nat.mul n w) j, mask (Nat.mul n w)))
      (pcomp n w (mask w) (ppow n w (mask w) (pidn n w) X (Nat.mod (Nat.succ j) (nat_lit 3)))
        (ppow n w (mask w) (pidn n w) Y (Nat.div (Nat.succ j) (nat_lit 3))))))

@[expose] noncomputable def srch (n w nb : Nat) (LR TR TRI : Nat → Nat) (BP DP : Nat) (TS : List Nat) :
    List Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ W B => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (leafOK w (mask w) nb TR BP W B TS))
    (fun E _ ih i W B => strictN (LR i) fun R =>
      level n w (mask w) (Nat.mul n w) TR TRI DP E i R W B ih)

end CFSG.KC.CentSrch

end
