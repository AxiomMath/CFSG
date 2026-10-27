module

public import Certificates.Data.Kernel.Spor.RawSl

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def lvOrbHdK (n w m : Nat) (kS root T R : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.blt kS (nat_lit 128),
  strictB (rcnt R) (fun c => strictB (stCnt T) (fun r =>
  bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble c n, bAnd(Nat.blt r (nat_lit 256),
  Nat.beq (rpt w m R (nat_lit 0)) root)))))))

@[expose] noncomputable def lvOrbKK (n w m nw : Nat) (S SI : Nat → Nat) (kS T R c r k : Nat) :
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

@[expose] noncomputable def lvOrbPtK (n w m nw : Nat) (S SI : Nat → Nat) (kS T R c r k : Nat) :
    Bool :=
  bAnd(bIf(Nat.blt k n, lvPosK w m nw R c k, true),
    bIf(Nat.blt k c, lvOrbKK n w m nw S SI kS T R c r k, true))

@[expose] noncomputable def lvOrbSlK (n w m nw : Nat) (S SI : Nat → Nat) (kS T R lo len : Nat) :
    Bool :=
  allN len (fun d => lvOrbPtK n w m nw S SI kS T R (rcnt R) (stCnt T) (Nat.add lo d))

end CFSG.KS.Raw

end
