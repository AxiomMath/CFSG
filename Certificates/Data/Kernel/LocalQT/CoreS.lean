module

public import Certificates.Data.Kernel.LocalQT.Core

public section

namespace CFSG.KC.LQT.Syl

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2

@[expose] noncomputable def idxK (x : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun y _ ih => Bool.rec (motive := fun _ => Nat) (Nat.succ ih) 0 (Nat.beq x y)) l

@[expose] noncomputable def linK (V u : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun j _ ih => Bool.rec (motive := fun _ => Nat) ih
    (Nat.xor ih (Nat.mod (Nat.shiftRight V (Nat.mul 4 j)) 16)) (bitK u j)) (List.range 4)

@[expose] noncomputable def cmLK (n : Nat) (B El : List Nat) (x : Nat) : Nat :=
  letN (inv n x) fun xi =>
  letN (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b _ ih j => Nat.lor (Nat.shiftLeft (idxK (mul n (mul n x b) xi) El) (Nat.mul 4 j))
      (ih (Nat.succ j))) B 0) fun V =>
  List.rec (motive := fun _ => Nat) 0 (fun u _ ih => Nat.add ih
    (Bool.rec (motive := fun _ => Nat) 0 (Nat.pow 2 u) (Nat.beq u (linK V u)))) (List.range 16)

@[expose] noncomputable def hypAx (n : Nat) (B : List Nat) (x : Nat) : Bool :=
  letB (cmLK n B (lstK n 4 B) x) fun m =>
    andB (notB (tvK m)) (impB (Nat.beq m 65535) (memL x (lstK n 4 B)))

@[expose] noncomputable def normK (n : Nat) (eR nR : List Nat) : Bool :=
  allL nR fun g => allL eR fun e => anyL (lstK n 4 eR) fun e' => Nat.beq (mul n g e) (mul n e' g)

@[expose] noncomputable def orbK (n : Nat) (G eR rT : List Nat) (nOrd kOrd : Nat) : Bool :=
  allBs [monoK (pairUpK rT), distinctS (List.map (maskK (fixK n (lstK n 4 eR))) (repsK n G rT)),
    Nat.beq kOrd (Nat.mul (lenL (repsK n G rT)) nOrd)]

end CFSG.KC.LQT.Syl

end
