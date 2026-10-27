module

public import Certificates.Data.Kernel.LocalQT.Sec
public import Certificates.Data.Kernel.Spor.F3Lane

public section

namespace CFSG.KC.LQT

open CFSG.KC.Ord CFSG.F3.Native CFSG.KS.F3L

@[expose] noncomputable def blkMask (P g k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft (nat_lit 1) g) (nat_lit 1))
    (fun i acc => Nat.lor acc (Nat.shiftLeft acc (Nat.mul P (Nat.shiftLeft (nat_lit 1) i)))) k

@[expose] noncomputable def gStage (w K s x : Nat) : Nat :=
  strictT (Nat.land x (blkMask (Nat.mul (nat_lit 2) (Nat.mul w (Nat.shiftLeft (nat_lit 1) s)))
      (Nat.shiftLeft (nat_lit 1) s) (Nat.sub K (Nat.succ s)))) fun a =>
    Nat.lor a (Nat.shiftRight (Nat.xor x a)
      (Nat.sub (Nat.mul w (Nat.shiftLeft (nat_lit 1) s)) (Nat.shiftLeft (nat_lit 1) s)))

@[expose] noncomputable def gathN (w K x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.land x (blkMask w (nat_lit 1) K))
    (fun s acc => strictT acc fun a => gStage w K s a) K

@[expose] noncomputable def gath3 (w K X : Nat) : V :=
  ⟨gathN w K X, gathN w K (Nat.shiftRight X (nat_lit 1))⟩

@[expose] noncomputable def eqV (a b : V) : Bool :=
  andB (Nat.beq a.p b.p) (Nat.beq a.m b.m)

@[expose] noncomputable def stepF3 (c : Lay) (K E : Nat) (V P : Nat → Nat) (n : Nat) : Bool :=
  strictB (P n) fun q => strictB (Nat.land q (nat_lit 1048575)) fun a =>
    strictB (Nat.shiftRight q (nat_lit 20)) fun b =>
      andB (Nat.blt a n) (andB (Nat.blt b n) (strictB (V n) fun X =>
        andB (validM c.p (Nat.mul c.d c.S) c.L c.H X)
          (eqV (gath3 c.w K X) (mulLane c.d E (gath3 c.w K (V a)) (gath3 c.w K (V b))))))

end CFSG.KC.LQT

end
