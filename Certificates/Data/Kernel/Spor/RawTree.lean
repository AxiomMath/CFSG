module

public import Certificates.Data.Kernel.Spor.RawSl

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def lvHdTK (n w m kS root T R : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.blt kS (nat_lit 128),
  strictB (rcnt R) (fun c => strictB (stCnt T) (fun r =>
  bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble c n, bAnd(Nat.blt r (nat_lit 256),
    Nat.beq (rpt w m R (nat_lit 0)) root)))))))

@[expose] noncomputable def lvKKT (n w m nw : Nat) (S SI : Nat → Nat) (kS T R c r k : Nat) :
    Bool :=
  bAnd(strictB (rpt w m R k) (fun p => bAnd(Nat.blt p n, Nat.beq (rpos w m nw R p) k)),
  bAnd(bIf(Nat.beq k (nat_lit 0), true,
    strictB (rpar w m nw R k) (fun pa => strictB (rlab n nw R k) (fun lb =>
    bAnd(Nat.blt pa k, bAnd(Nat.blt lb r,
      Nat.beq (pg w m (letterK S SI kS (stAt T lb)) (rpt w m R pa)) (rpt w m R k)))))),
  bAnd(bIf(Nat.beq k (nat_lit 0), true, bIf(Nat.blt (Nat.succ k) c,
    lexLtK (rpar w m nw R k) (rlab n nw R k) (rpar w m nw R (Nat.succ k))
      (rlab n nw R (Nat.succ k)), true)),
  strictB (rpt w m R k) (fun p => allN r (fun j =>
    strictB (rpos w m nw R (pg w m (letterK S SI kS (stAt T j)) p)) (fun k' =>
    bAnd(Nat.blt k' c, bIf(Nat.beq k' (nat_lit 0), true,
      bIf(lexLtK k j (rpar w m nw R k') (rlab n nw R k'), false, true)))))))))

@[expose] noncomputable def lvPtTK (n w m nw : Nat) (S SI : Nat → Nat) (kS T R c r k : Nat) :
    Bool :=
  bAnd(bIf(Nat.blt k n, lvPosK w m nw R c k, true),
    bIf(Nat.blt k c, lvKKT n w m nw S SI kS T R c r k, true))

@[expose] noncomputable def lvSlTK (n w m nw : Nat) (S SI : Nat → Nat) (kS T R lo len : Nat) :
    Bool :=
  allN len (fun d => lvPtTK n w m nw S SI kS T R (rcnt R) (stCnt T) (Nat.add lo d))

@[expose] noncomputable def invLetterK (S SI : Nat → Nat) (kS l : Nat) : Nat :=
  nIf(Nat.blt l kS, SI l, S (Nat.sub l kS))

@[expose] noncomputable def mapB (w m nb l s G : Nat) : Nat :=
  strictN G (fun G => foldUp nb (fun t acc => Nat.lor acc (Nat.shiftLeft
    (nIf(Nat.blt l t, pg w m s (pg w m G t), nat_lit 0)) (Nat.mul w t))) (nat_lit 0))

@[expose] noncomputable def walkT (n w m nw nb : Nat) (S SI : Nat → Nat) (kS T R l : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ G => G)
    (fun _ ih h G => nIf(Nat.beq h (nat_lit 0), G,
      strictN (ih (rpar w m nw R h) G) (fun G' =>
        mapB w m nb l (letterK S SI kS (stAt T (rlab n nw R h))) G')))

@[expose] noncomputable def walkIT (n w m nw nb : Nat) (S SI : Nat → Nat) (kS T R l : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ G => G)
    (fun _ ih k G => nIf(Nat.beq k (nat_lit 0), G,
      strictN (mapB w m nb l (invLetterK S SI kS (stAt T (rlab n nw R k))) G)
        (ih (rpar w m nw R k))))

@[expose] noncomputable def siftBK (n w m nw nb : Nat) (S SI LR ST : Nat → Nat) (kS : Nat) :
    Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih l G => strictB (LR l) (fun R => strictB (ST l) (fun T =>
      strictB (rpos w m nw R (pg w m G l)) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (walkIT n w m nw nb S SI kS T R l k k G) (ih (Nat.succ l)), false)))))

@[expose] noncomputable def schBPt (n w m nw nb : Nat) (S SI LR ST : Nat → Nat) (kS BP i h : Nat) :
    Bool :=
  strictB (LR i) (fun R => strictB (ST i) (fun T => strictB (rcnt R) (fun c =>
  strictB (walkT n w m nw nb S SI kS T R i h h BP) (fun G => strictB (rpt w m R h) (fun p =>
  allN (stCnt T) (fun j => strictB (letterK S SI kS (stAt T j)) (fun s =>
    strictB (rpos w m nw R (pg w m s p)) (fun k => bAnd(Nat.blt k c,
      siftBK n w m nw nb S SI LR ST kS (Nat.sub nb (Nat.succ i)) (Nat.succ i)
        (walkIT n w m nw nb S SI kS T R i k k (mapB w m nb i s G)))))))))))

@[expose] noncomputable def schBK (n w m nw nb : Nat) (S SI LR ST : Nat → Nat) (kS BP i h₀ cnt : Nat) :
    Bool :=
  strictB (rcnt (LR i)) (fun c => allN cnt (fun d => strictB (Nat.add h₀ d) (fun h =>
    bIf(Nat.blt h c, schBPt n w m nw nb S SI LR ST kS BP i h, true))))

end CFSG.KS.Raw

end
