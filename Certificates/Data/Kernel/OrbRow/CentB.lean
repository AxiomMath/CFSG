module

public import Certificates.Data.Kernel.OrbRow.Cent

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp

@[expose] noncomputable def cntK (L : List Nat) (f : Nat → Bool) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => nIf(f x, Nat.succ ih, ih)) L

@[expose] noncomputable def cntN (k : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun t ih => nIf(f t, Nat.succ ih, ih)) k

@[expose] noncomputable def inD (D x : Nat) : Bool :=
  bIf(Nat.beq (depD D x) (nat_lit 255), false, true)

@[expose] noncomputable def degK (n w m : Nat) (S : List Nat) (k lv b D : Nat) (F : List Nat)
    (p dg : Nat) (wd : List Nat) : Bool :=
  strictB (posWordK n w (getS S) wd) fun u => strictB (CFSG.KS.pinvS n w m u) fun ui =>
    bAnd(lettersK k lv wd, bAnd(Nat.beq (pg w m u b) p, bAnd(permOK n w m (Nat.mul n w) u ui,
      Nat.beq (cntK F fun q => inD D (pg w m ui q)) dg)))

@[expose] noncomputable def capK (D : Nat) (F : List Nat) (c : Nat) : Bool :=
  Nat.beq (cntK F (inD D)) c

@[expose] noncomputable def incK (Q : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun q _ ih i prev => bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt prev q),
      ih (Nat.succ i) q)) Q

@[expose] noncomputable def regK (n w m : Nat) (S : List Nat) (k lv b D : Nat) (Q : List Nat)
    (V : List (List Nat)) (cnt x cc : Nat) : Bool :=
  bAnd(Nat.beq (lenS Q) cnt, bAnd(incK Q (nat_lit 0) (nat_lit 0),
  bAnd(allN cnt (fun t => strictB (getS Q t) fun q =>
    bAnd(inD D q, bAnd(lettersK k lv (getLs V t),
      Nat.beq (pg w m (posWordK n w (getS S) (getLs V t)) b) q))),
    Nat.beq (cntN cnt fun t => commOK n w m (posWordK n w (getS S) (getLs V t)) x) cc)))

end CFSG.KC.OrbRow

end
