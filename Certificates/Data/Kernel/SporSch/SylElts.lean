module

public import Certificates.Data.Kernel.SporSch.MathieuBT

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11

@[expose] noncomputable def memL (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq y x, true, ih)) L

@[expose] noncomputable def allL (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(f y, ih)) L

@[expose] noncomputable def incL (p : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun y _ ih q => bAnd(Nat.blt q y, ih y)) L p

@[expose] noncomputable def eltK (n w m nw idn : Nat) (LR TRI : Nat → Nat) (BP nb : Nat)
    (XL RL : List Nat) (mo X O J C : Nat) : Bool :=
  bAnd(canonK n w m nw X, bAnd(siftK n w m nw idn LR TRI BP nb 0 X,
    bAnd(allL (fun Y => memL (pcomp n w m X Y) XL) XL, bAnd(ordIs n w m idn X (Nat.pred O),
    bIf(Nat.beq O mo, bAnd(Nat.blt J RL.length, bAnd(canonK n w m nw C,
      bAnd(siftK n w m nw idn LR TRI BP nb 0 C,
        Nat.beq (pcomp n w m C (RL.getD J 0)) (pcomp n w m X C)))), true)))))

end CFSG.KS.SporSch.MBT

end
