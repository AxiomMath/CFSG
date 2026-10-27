module

public import Certificates.Data.Kernel.Spor.RawTree
public import Certificates.Data.Kernel.Spor.BaseEq

public section

namespace CFSG.KS.Co2Third

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.BaseEq

@[expose] noncomputable def walkIK (n w m nw : Nat) (S SI : Nat → Nat) (kS T R : Nat) (f : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ z => z)
    (fun _ ih k z => nIf(Nat.beq k (nat_lit 0), z,
      ih (rpar w m nw R k) (pg w m (invLetterK S SI kS (stAt T (rlab n nw R k))) z))) f

@[expose] noncomputable def mIK (n w m nw : Nat) (S SI : Nat → Nat) (kS T R : Nat)
    (inO : Nat → Bool) (F : Nat → Nat) (cF k : Nat) : Nat :=
  cntN cF fun i => inO (walkIK n w m nw S SI kS T R k k (F i))

@[expose] noncomputable def candK (n w m nw : Nat) (S SI : Nat → Nat) (kS T R : Nat)
    (inO : Nat → Bool) (F : Nat → Nat) (cF ref : Nat) : Nat :=
  cntN cF fun i => strictB (rpos w m nw R (F i)) fun k =>
    bAnd(Nat.blt k (rcnt R), Nat.beq (mIK n w m nw S SI kS T R inO F cF k) ref)

@[expose] noncomputable def fixListK (n w m U : Nat) (F : Nat → Nat) (cF : Nat) : Bool :=
  bAnd(allN cF fun i => bAnd(Nat.blt (F i) n, Nat.beq (pg w m U (F i)) (F i)),
    bAnd(allN (Nat.sub cF (nat_lit 1)) fun i => Nat.blt (F i) (F (Nat.succ i)),
      Nat.beq (cntN n fun z => Nat.beq (pg w m U z) z) cF))

@[expose] noncomputable def fixCntK (w m R U : Nat) : Nat :=
  cntN (rcnt R) fun k => strictB (rpt w m R k) fun x => Nat.beq (pg w m U x) x

@[expose] noncomputable def inK (O : Nat → Nat) (c z : Nat) : Bool :=
  not (allN c fun i => not (Nat.beq (O i) z))

@[expose] noncomputable def closK (w m : Nat) (S SI : Nat → Nat) (kS T : Nat) (O : Nat → Nat)
    (c : Nat) : Bool :=
  allN c fun i => allN (stCnt T) fun j => inK O c (pg w m (letterK S SI kS (stAt T j)) (O i))

end CFSG.KS.Co2Third

end
