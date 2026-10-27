module

public import Certificates.Data.Kernel.L34K
public import Certificates.Data.SolMaxSixGen

public section

namespace CFSG.KC.SolMax

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KLie.CT (andB orB notB)

@[expose] def gsOf (c : CFSG.ComponentClassification.SolMax.SixGen.Swaps ×
    List CFSG.ComponentClassification.SolMax.SixGen.Swaps × Nat) : Array CFSG.PSL3Four.Native.Tab :=
  (c.2.1.map fun l =>
    CFSG.ComponentClassification.SolMax.SixGen.tabOf
      (CFSG.ComponentClassification.SolMax.SixGen.permOf l)).toArray

@[expose] noncomputable def pc9 (x y : Nat) : Nat := pcomp 9 4 (mask 4) x y

@[expose] noncomputable def e9 : Nat := pidn 9 4

@[expose] noncomputable def cntK (f : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => strictN acc fun a => Bool.rec (motive := fun _ => Nat) (Nat.succ a) a (f i)) n

@[expose] noncomputable def suppK (x : Nat) : Nat := cntK (fun i => Nat.beq (pg 4 (mask 4) x i) i) 9

@[expose] noncomputable def commK (k : Nat) (G : Nat → Nat) (U : Nat) : Bool :=
  allN k fun j => Nat.beq (pc9 (G j) U) (pc9 U (G j))

@[expose] noncomputable def restXK (cnt : Nat) (T : Nat → Nat) : Bool :=
  allN cnt fun i => strictB (T i) fun y => strictB (pc9 y y) fun y2 =>
    orB (Nat.beq y2 e9) (orB (notB (Nat.beq (pc9 y2 y2) e9))
      (orB (Nat.blt (suppK y) 6) (Nat.blt (suppK y2) 6)))

@[expose] noncomputable def bigK (y : Nat) : Bool :=
  andB (Nat.beq (pc9 y y) e9) (andB (notB (Nat.beq y e9)) (Nat.ble 6 (suppK y)))

@[expose] noncomputable def restYK (cnt : Nat) (T : Nat → Nat) : Bool :=
  allN cnt fun i => strictB (T i) fun a => orB (notB (bigK a)) (allN cnt fun j =>
    strictB (T j) fun b => orB (notB (bigK b)) (orB (Nat.beq a b)
      (orB (notB (Nat.beq (pc9 a b) (pc9 b a))) (Nat.blt (suppK (pc9 a b)) 6))))

@[expose] noncomputable def admK (u w : Nat) : Bool :=
  orB (Nat.beq (pc9 w w) u) (andB (Nat.beq (pc9 w w) e9)
    (andB (Nat.ble 5 (suppK w)) (Nat.ble 5 (suppK (pc9 w u)))))

@[expose] noncomputable def linkK (u a b : Nat) : Bool :=
  andB (Nat.beq (pc9 a b) (pc9 b a))
    (andB (notB (Nat.beq (pc9 a b) e9)) (notB (Nat.beq (pc9 a b) u)))

@[expose] noncomputable def restZK (u cnt : Nat) (T : Nat → Nat) : Bool :=
  allN cnt fun i => strictB (T i) fun a => orB (notB (admK u a)) (allN cnt fun j =>
    strictB (T j) fun b => orB (notB (admK u b)) (orB (notB (linkK u a b)) (allN cnt fun k =>
      strictB (T k) fun c => orB (notB (admK u c))
        (orB (notB (andB (linkK u a c) (linkK u b c))) (allN cnt fun l =>
          strictB (T l) fun d => orB (notB (admK u d))
            (notB (andB (linkK u a d) (andB (linkK u b d) (linkK u c d)))))))))

end CFSG.KC.SolMax

end
