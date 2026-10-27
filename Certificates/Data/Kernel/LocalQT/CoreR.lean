module

public import Certificates.Data.Kernel.LocalQT.CoreS

public section

namespace CFSG.KC.LQT.Syl

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2

@[expose] noncomputable def chooseK (q k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun i acc =>
    Nat.div (Nat.mul acc (Nat.sub q i)) (Nat.succ i)) k

@[expose] noncomputable def rankM (n m : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk 0 0) (fun q st =>
    Bool.rec (motive := fun _ => Nat × Nat) st
      (Prod.mk (Nat.add st.1 (chooseK q (Nat.succ st.2))) (Nat.succ st.2))
      (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 q)))) n).1

@[expose] noncomputable def colexK (n : Nat) (T : List Nat) (r : Nat) : Nat := rankM n (maskK T r)

@[expose] noncomputable def distinctR (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih seen => letB (Nat.shiftLeft 1 x) fun b =>
      andB (Nat.beq (Nat.land seen b) 0) (ih (Nat.lor seen b))) l 0

@[expose] noncomputable def orbN (n : Nat) (G eR rT : List Nat) (nOrd kOrd : Nat) : Bool :=
  andB (monoK (pairUpK rT))
    ((fun R => andB (distinctR (List.map (colexK n (fixK n (lstK n 4 eR))) R))
      (Nat.beq kOrd (Nat.mul (lenL R) nOrd))) (repsK n G rT))

end CFSG.KC.LQT.Syl

end
