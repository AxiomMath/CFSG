module

public import Certificates.Data.Kernel.LocalQT.Sec

public section

namespace CFSG.KC.LocalComp.ElemParts

open CFSG.KC.LQT CFSG.KC.Ord

@[expose] noncomputable def stepIs (P : Nat → Nat) (N t a b : Nat) : Bool :=
  andB (Nat.ble 3 t) (andB (Nat.blt t N) (Nat.beq (P t) (Nat.add a (Nat.shiftLeft b 20))))

@[expose] noncomputable def cubeK (c : Lay) (V P : Nat → Nat) (N o sq cu : Nat) : Bool :=
  andB (Nat.blt o N) (andB (stepIs P N sq o o) (andB (stepIs P N cu sq o) (Nat.beq (V cu) c.ONE)))

@[expose] noncomputable def pairK (V P : Nat → Nat) (N a b pab pba : Nat) : Bool :=
  andB (stepIs P N pab a b) (andB (stepIs P N pba b a) (Nat.beq (V pab) (V pba)))

@[expose] noncomputable def kerK (c : Lay) (V : Nat → Nat) (O W : Nat → Nat) (r lo cnt : Nat) :
    Bool :=
  allLt cnt fun k => strictB (Nat.add lo k) fun n =>
    Bool.rec (motive := fun _ => Bool) true
      (strictB (W (Nat.succ n)) fun t =>
        andB (Nat.blt t c.d) (notB (Nat.beq
          (digApp c (nat_lit 3) (fun i => V (O i)) r (nat_lit 0) (Nat.succ n) (c.unit t))
          (c.unit t))))
      (Nat.blt n (Nat.sub (Nat.pow (nat_lit 3) r) (nat_lit 1)))

end CFSG.KC.LocalComp.ElemParts

end
