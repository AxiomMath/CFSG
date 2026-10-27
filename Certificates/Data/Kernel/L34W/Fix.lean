module

public import Certificates.Data.Kernel.L34W.ModK
public import Certificates.Data.GrSLitL34Sec5SWIsoCheck

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

@[expose] noncomputable def betaK (A : Nat → Nat) (b i x : Nat) : Nat :=
  strictN (pg (nat_lit 10) (mask 10) b (Nat.div x (nat_lit 16))) fun v =>
  strictN (ent A i (nat_lit 64)) fun p =>
  strictN (ent A i (nat_lit 65)) fun q =>
  strictN (Nat.mod (Nat.div x (nat_lit 4)) (nat_lit 4)) fun a =>
  strictN (Nat.mod x (nat_lit 4)) fun c =>
    mk (Nat.div v (nat_lit 16))
      (Nat.add (Nat.mod (Nat.div v (nat_lit 4)) (nat_lit 4))
        (Nat.add (Nat.mul a (Nat.div (Nat.mod p (nat_lit 48)) (nat_lit 12)))
          (Nat.mul c (Nat.div (Nat.mod q (nat_lit 48)) (nat_lit 12)))))
      (Nat.add (Nat.mod v (nat_lit 4))
        (Nat.add (Nat.mul a (Nat.div (Nat.mod p (nat_lit 12)) (nat_lit 3)))
          (Nat.mul c (Nat.div (Nat.mod q (nat_lit 12)) (nat_lit 3)))))

@[expose] noncomputable def fixC (A : Nat → Nat) (b i m x : Nat) : Bool := eqC m (betaK A b i x) x

@[expose] noncomputable def d1W (T A : Nat → Nat) (m i b i' b' x y : Nat) : Bool :=
  bAnd(bAnd(bAnd(Nat.blt x (nat_lit 1024), Nat.blt y (nat_lit 1024)), bNot (eqC m y x)),
    bAnd(bAnd(bAnd(fixC A b i m x, fixC A b' i' m x), isInvC T m x),
      bAnd(bAnd(fixC A b i m y, fixC A b' i' m y), isInvC T m y)))

@[expose] noncomputable def d1One (T A OT BT CM W : Nat → Nat) (m k : Nat) : Bool :=
  allN (nat_lit 144) fun j => strictB (OT j) fun n => strictB (BT j) fun b =>
    strictB (CM j) fun c => strictB (W (Nat.add (Nat.mul (nat_lit 144) k) j)) fun w =>
      allN (nat_lit 144) fun j' => bIf(hasBit c j',
        d1W T A m (Nat.div n (nat_lit 64)) b (Nat.div (OT j') (nat_lit 64)) (BT j')
          (pg (nat_lit 10) (mask 10) w (Nat.mul (nat_lit 2) j'))
          (pg (nat_lit 10) (mask 10) w (Nat.add (Nat.mul (nat_lit 2) j') (nat_lit 1))), true)

@[expose] noncomputable def dP (T A : Nat → Nat) (m i b k x : Nat) : Bool :=
  bAnd(bAnd(Nat.blt x (nat_lit 1024), fixC A b i m x),
    bAnd(isInvC T m x, commC T m x (Nat.mul (nat_lit 16) k)))

@[expose] noncomputable def dist3 (m x y z : Nat) : Bool :=
  bAnd(bNot (eqC m y x), bAnd(bNot (eqC m z x), bNot (eqC m z y)))

@[expose] noncomputable def exK (q : Nat) : Nat := nIf(Nat.beq q (nat_lit 0), nat_lit 0, nat_lit 2)

@[expose] noncomputable def cycMask : Nat := nat_lit 32721

@[expose] noncomputable def dW (T A : Nat → Nat) (m q i b ty k w : Nat) : Bool :=
  strictB (pg (nat_lit 10) (mask 10) w (nat_lit 0)) fun tag =>
  strictB (pg (nat_lit 10) (mask 10) w (nat_lit 1)) fun x =>
  strictB (pg (nat_lit 10) (mask 10) w (nat_lit 2)) fun y =>
  strictB (pg (nat_lit 10) (mask 10) w (nat_lit 3)) fun z =>
  strictB (pg (nat_lit 10) (mask 10) w (nat_lit 4)) fun u =>
  bIf(Nat.beq tag (nat_lit 0),
    bAnd(dP T A m i b k x,
      bAnd(bNot (Nat.beq (Nat.div x (nat_lit 16)) (nat_lit 0)), bNot (Nat.beq (Nat.div x (nat_lit 16)) k))),
  bIf(Nat.beq tag (nat_lit 1),
    bAnd(bAnd(bAnd(dP T A m i b k x, dP T A m i b k y), bAnd(dP T A m i b k z, dP T A m i b k u)),
      bAnd(dist3 m x y z, bAnd(bNot (eqC m u x), bAnd(bNot (eqC m u y), bNot (eqC m u z))))),
  bIf(Nat.beq tag (nat_lit 2),
    bAnd(bAnd(bNot (Nat.beq k (nat_lit 0)), Nat.beq ty (exK q)),
      bAnd(hasBit cycMask q, bIf(Nat.beq q (nat_lit 14), true,
        bAnd(bAnd(dP T A m i b k x, dP T A m i b k y), bAnd(dP T A m i b k z, dist3 m x y z))))),
    false)))

@[expose] noncomputable def dOne (T A OT BT LF TY W : Nat → Nat) (m q : Nat) : Bool :=
  strictB (LF q) fun lf => allN (nat_lit 144) fun j => strictB (OT j) fun n =>
    bIf(hasBit lf (Nat.div n (nat_lit 64)),
      strictB (BT j) fun b => strictB (TY j) fun ty =>
        strictB (W (Nat.add (Nat.mul (nat_lit 144) q) j)) fun w =>
          allN (nat_lit 64) fun k => bIf(kvK T BT j k,
            dW T A m q (Nat.div n (nat_lit 64)) b ty k
              (Nat.shiftRight w (Nat.mul (nat_lit 50) k)), true),
      true)

@[expose] def liftsQ (kb : List Bool) (p q : ℕ) : Bool :=
  z4.all fun a => z4.all fun b => !inKB kb a b ||
    inKB kb (a * ((quad p).2.1 : ZMod 4) + b * ((quad q).2.1 : ZMod 4))
      (a * ((quad p).2.2.1 : ZMod 4) + b * ((quad q).2.2.1 : ZMod 4))

@[expose] noncomputable def lfOK (A LF : Nat → Nat) : Bool :=
  allN (nat_lit 15) fun q => allN (nat_lit 36) fun i =>
    bIf(liftsQ (kbOfMask (kbMasks.getD q 0)) (ent A i (nat_lit 64)) (ent A i (nat_lit 65)),
      hasBit (LF q) i, true)

@[expose] noncomputable def tyOK (OT TY : Nat → Nat) : Bool :=
  allN (nat_lit 144) fun j => Nat.beq (typeOf (Nat.mod (OT j) (nat_lit 64)) (Nat.div (OT j) (nat_lit 64))) (TY j)

end CFSG.KC.L34W

end
