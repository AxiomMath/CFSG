module

public import Certificates.Data.Kernel.G24Key

public section

namespace CFSG.KC.G24Word

open CFSG.KC.Enum CFSG.KC.G24Key

@[expose] noncomputable def letC (A AI B BI c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 2), A, nIf(Nat.beq c (nat_lit 3), AI, nIf(Nat.beq c (nat_lit 4), B, BI)))

@[expose] noncomputable def lettersK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => bAnd(Nat.ble (nat_lit 2) c, bAnd(Nat.ble c (nat_lit 5), ih))) w

@[expose] noncomputable def wF (L : Nat → Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun c _ ih p => strictN (ih p) (fun q => ap (L c) q)) w p

@[expose] noncomputable def wI (LI : Nat → Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun c _ ih p => strictN (ap (LI c) p) ih) w p

@[expose] noncomputable def sel3 (a b c t : Nat) : Nat :=
  nIf(Nat.beq t (nat_lit 0), a, nIf(Nat.beq t (nat_lit 1), b, c))

@[expose] noncomputable def normJ (L LI G KT NI : Nat → Nat) (J n : Nat) (w : List Nat) (j : Nat) :
    Bool :=
  bAnd(lettersK w,
    strictB (wI LI w (nat_lit 0)) (fun q0 => strictB (wI LI w (nat_lit 1)) (fun q1 =>
    strictB (wI LI w (nat_lit 2)) (fun q2 =>
    allN J (fun i => strictB (NI (Nat.add (Nat.mul J j) i)) (fun k =>
      bAnd(Nat.blt k n, Nat.beq (KT k)
        (keyOf (fun t => wF L w (ap (G i) (sel3 q0 q1 q2 t)))))))))))

@[expose] noncomputable def fixB (L : Nat → Nat) (w : List Nat) : Bool :=
  allN (nat_lit 3) (fun t => Nat.beq (wF L w t) t)

@[expose] noncomputable def diffB (L : Nat → Nat) (v w : List Nat) (p : Nat) : Bool :=
  bIf(Nat.beq (wF L v p) (wF L w p), false, true)

end CFSG.KC.G24Word

end
