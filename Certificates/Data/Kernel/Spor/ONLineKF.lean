module

public import Certificates.Data.Kernel.Spor.ONKF
public import Certificates.Data.Kernel.Spor.ONLineK

public section

namespace CFSG.KS.ONF

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def lineAtF (KL LP : Nat → Nat) (TA TB : Nat → Nat) (cnt : Nat)
    (AL BL : Nat → Nat) (n h : Nat) : Bool :=
  strictB (key KL h) fun x => strictB (tab AL h) fun a => strictB (tab BL h) fun b =>
    bAnd(canon x, bAnd(lead1 x (tab LP h), bAnd(Nat.blt a n, bAnd(Nat.blt b n,
      bAnd(pmEq (key KL a) (mvF TA cnt x), pmEq (key KL b) (mvF TB cnt x))))))

@[expose] noncomputable def lineRangeF (KL LP : Nat → Nat) (TA TB : Nat → Nat) (cnt : Nat)
    (AL BL : Nat → Nat) (n lo len : Nat) : Bool :=
  allBlk lo (lineAtF KL LP TA TB cnt AL BL n) len

end CFSG.KS.ONF

end
