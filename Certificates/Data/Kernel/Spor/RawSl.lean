module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def lvHdK (n w m nw idn : Nat) (TR : Nat → Nat) (kS root T R : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.blt kS (nat_lit 128),
  strictB (rcnt R) (fun c => strictB (stCnt T) (fun r => strictB (roff n nw R) (fun o =>
  bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble c n, bAnd(Nat.blt r (nat_lit 256),
  bAnd(Nat.beq (rpt w m R (nat_lit 0)) root, Nat.beq (TR o) idn)))))))))

@[expose] noncomputable def lvPosK (w m nw R c z : Nat) : Bool :=
  strictB (rpos w m nw R z) (fun q => bIf(Nat.blt q c, Nat.beq (rpt w m R q) z, true))

@[expose] noncomputable def lvKK (n w m nw : Nat) (S SI TR TRI : Nat → Nat) (kS T R c r o k : Nat) :
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
    eq2 n w m (TR (Nat.add o k)) (letterK S SI kS (stAt T (rlab n nw R k)))
      (TR (Nat.add o (rpar w m nw R k)))),
  permOK n w m nw (TR (Nat.add o k)) (TRI (Nat.add o k)))))))

@[expose] noncomputable def lvPtK (n w m nw : Nat) (S SI TR TRI : Nat → Nat) (kS T R c r o k : Nat) :
    Bool :=
  bAnd(bIf(Nat.blt k n, lvPosK w m nw R c k, true),
    bIf(Nat.blt k c, lvKK n w m nw S SI TR TRI kS T R c r o k, true))

@[expose] noncomputable def lvSlK (n w m nw : Nat) (S SI TR TRI : Nat → Nat) (kS T R lo len : Nat) :
    Bool :=
  allN len (fun d => lvPtK n w m nw S SI TR TRI kS T R (rcnt R) (stCnt T) (roff n nw R)
    (Nat.add lo d))

end CFSG.KS.Raw

end
