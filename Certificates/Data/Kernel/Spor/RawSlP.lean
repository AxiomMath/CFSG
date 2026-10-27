module

public import Certificates.Data.Kernel.Spor.RawSl

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def invP (n w m nw p q : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight p nw) (nat_lit 0), bAnd(Nat.beq (Nat.shiftRight q nw) (nat_lit 0),
    bAnd(Nat.blt (pg w m p (nat_lit 0)) n, Nat.beq (pcomp n w m q p) (pidn n w))))

@[expose] noncomputable def lvKKP (n w m nw : Nat) (S SI TR TRI : Nat → Nat) (kS T R c r o k : Nat) :
    Bool :=
  bAnd(strictB (rpt w m R k) (fun p => bAnd(Nat.blt p n, Nat.beq (rpos w m nw R p) k)),
  bAnd(bIf(Nat.beq k (nat_lit 0), true,
    strictB (rpar w m nw R k) (fun pa => strictB (rlab n nw R k) (fun lb =>
    bAnd(Nat.blt pa k, bAnd(Nat.blt lb r,
      Nat.beq (pg w m (letterK S SI kS (stAt T lb)) (rpt w m R pa)) (rpt w m R k)))))),
  bAnd(bIf(Nat.beq k (nat_lit 0), true, bIf(Nat.blt (Nat.succ k) c,
    lexLtK (rpar w m nw R k) (rlab n nw R k) (rpar w m nw R (Nat.succ k))
      (rlab n nw R (Nat.succ k)), true)),
  bAnd(strictB (rpt w m R k) (fun p => allN r (fun j =>
    strictB (rpos w m nw R (pg w m (letterK S SI kS (stAt T j)) p)) (fun k' =>
    bAnd(Nat.blt k' c, bIf(Nat.beq k' (nat_lit 0), true,
      bIf(lexLtK k j (rpar w m nw R k') (rlab n nw R k'), false, true)))))),
  bAnd(bIf(Nat.beq k (nat_lit 0), true,
    Nat.beq (TR (Nat.add o k)) (pcomp n w m (letterK S SI kS (stAt T (rlab n nw R k)))
      (TR (Nat.add o (rpar w m nw R k))))),
  invP n w m nw (TR (Nat.add o k)) (TRI (Nat.add o k)))))))

@[expose] noncomputable def lvPtKP (n w m nw : Nat) (S SI TR TRI : Nat → Nat) (kS T R c r o k : Nat) :
    Bool :=
  bAnd(bIf(Nat.blt k n, lvPosK w m nw R c k, true),
    bIf(Nat.blt k c, lvKKP n w m nw S SI TR TRI kS T R c r o k, true))

@[expose] noncomputable def lvSlKP (n w m nw : Nat) (S SI TR TRI : Nat → Nat) (kS T R lo len : Nat) :
    Bool :=
  allN len (fun d => lvPtKP n w m nw S SI TR TRI kS T R (rcnt R) (stCnt T) (roff n nw R)
    (Nat.add lo d))

end CFSG.KS.Raw

end
