module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.IE

open CFSG.KC.Enum

@[expose] noncomputable def lexB (a b c d : Nat) : Bool :=
  bIf(Nat.blt a c, true, bAnd(Nat.beq a c, Nat.blt b d))

@[expose] noncomputable def imgAt (I : Nat → Nat) (k t : Nat) : Nat :=
  I (Nat.add (Nat.mul (nat_lit 154) k) t)

@[expose] noncomputable def stepEq (G : Nat → Nat → Nat) (I : Nat → Nat) (j h q : Nat) : Bool :=
  allN (nat_lit 154) fun t => Nat.beq (G j (imgAt I h t)) (imgAt I q t)

@[expose] noncomputable def ieAt (G : Nat → Nat → Nat) (P I PAR LAB POS : Nat → Nat)
    (ng cnt h : Nat) : Bool :=
  bAnd(bIf(Nat.beq h (nat_lit 0),
      bAnd(Nat.beq (PAR (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (LAB (nat_lit 0)) (nat_lit 0),
        allN (nat_lit 154) fun t => Nat.beq (imgAt I (nat_lit 0) t) (P t))),
      strictB (PAR h) fun p => strictB (LAB h) fun l =>
        bAnd(Nat.blt p h, bAnd(Nat.blt l ng, bAnd(stepEq G I l p h,
          bIf(Nat.blt (Nat.succ h) cnt, lexB p l (PAR (Nat.succ h)) (LAB (Nat.succ h)), true))))),
    allN ng fun j => strictB (POS (Nat.add (Nat.mul h ng) j)) fun q =>
      bAnd(Nat.blt q cnt, bAnd(stepEq G I j h q,
        bIf(Nat.beq q (nat_lit 0), true, Bool.not (lexB h j (PAR q) (LAB q))))))

@[expose] noncomputable def ieSl (G : Nat → Nat → Nat) (P I PAR LAB POS : Nat → Nat)
    (ng cnt lo len : Nat) : Bool :=
  allN len fun d => strictB (Nat.add lo d) fun h =>
    bIf(Nat.blt h cnt, ieAt G P I PAR LAB POS ng cnt h, true)

@[expose] noncomputable def eltR (G : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (f : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => nIf(Nat.beq k (nat_lit 0), x, G (LAB k) (ih (PAR k) x))) f

@[expose] noncomputable def fpF (f : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => Nat.add (Nat.mul acc (nat_lit 262144)) (f t)) m

@[expose] noncomputable def fpK (I : Nat → Nat) (m k : Nat) : Nat := fpF (imgAt I k) m

@[expose] noncomputable def distK (FP : Nat → Nat) (cnt : Nat) : Bool :=
  allN cnt fun a => allN a fun b => Bool.not (Nat.beq (FP a) (FP b))

end CFSG.KS.IE

end
