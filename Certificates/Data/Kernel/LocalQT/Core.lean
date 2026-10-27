module

public import Certificates.Data.Kernel.LocalQT.SylL

public section

namespace CFSG.KC.LQT.Syl

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2

@[expose] noncomputable def sortN (l : List Nat) : List Nat :=
  List.flatten (Nat.rec (motive := fun _ => List (List Nat)) (List.map (fun x => [x]) l)
    (fun _ ih => passK ih) 17)

@[expose] noncomputable def dedupS (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => Option Nat → List Nat) (fun _ => [])
    (fun x _ ih o => Option.rec (motive := fun _ => List Nat) (List.cons x (ih (some x)))
      (fun y => Bool.rec (motive := fun _ => List Nat) (List.cons x (ih (some x))) (ih (some x))
        (Nat.beq x y)) o) l none

@[expose] noncomputable def dropLt (x : Nat) (ys : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun y ys' ih =>
    Bool.rec (motive := fun _ => List Nat) (List.cons y ys') ih (Nat.blt y x)) ys

@[expose] noncomputable def diffS (xs ys : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun x _ ih ys => Bool.rec (motive := fun _ => List Nat) (List.cons x (ih (dropLt x ys)))
      (ih (dropLt x ys))
      (List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y x) (dropLt x ys))) xs ys

@[expose] noncomputable def bfsStepK (n : Nat) (gens : List Nat) (st : List Nat × List Nat) :
    List Nat × List Nat :=
  Prod.rec (motive := fun _ => List Nat × List Nat) (fun S F =>
    Prod.mk (mergeK S (diffS (dedupS (sortN (List.flatten
      (List.map (fun x => List.map (mul n x) gens) F)))) S))
      (diffS (dedupS (sortN (List.flatten (List.map (fun x => List.map (mul n x) gens) F)))) S))
    st

@[expose] noncomputable def bfsK (n : Nat) (gens : List Nat) (r : Nat) : List Nat :=
  (Nat.rec (motive := fun _ => List Nat × List Nat) ([one n], [one n])
    (fun _ ih => bfsStepK n gens ih) r).1

@[expose] noncomputable def pairUpK (rT : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List Nat → List (Nat × Nat)) (fun _ => [])
    (fun x _ ih pend => List.rec (motive := fun _ => List (Nat × Nat)) (ih [x])
      (fun p _ _ => List.cons (p, x) (ih [])) pend) rT []

@[expose] noncomputable def repsK (n : Nat) (G rT : List Nat) : List Nat :=
  bfsQ (fun x g => mul n g x) (one n) G (one n) (pairUpK rT)

@[expose] noncomputable def fixK (n : Nat) (E : List Nat) : List Nat :=
  List.filter (fun p => allL E fun e => Nat.beq (img e p) p) (List.range n)

@[expose] noncomputable def maskK (T : List Nat) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.lor (Nat.pow 2 (img r p)) ih) T

@[expose] noncomputable def eK (n : Nat) (eR : List Nat) : Bool :=
  allBs [Nat.ble n 32, Nat.beq (lenL eR) 4,
    eqL (sortN (lstK n 4 eR)) (bfsK n eR 16), distinctS (lstK n 4 eR),
    allL eR (fun e => Nat.beq (mul n e e) (one n)), allL eR fun e => allL eR fun f => comm n e f,
    allL (bfsK n eR 16) fun x => allL eR fun g => memL (mul n x g) (bfsK n eR 16)]

@[expose] noncomputable def bitK (m i : Nat) : Bool := Nat.beq (Nat.mod (Nat.shiftRight m i) 2) 1

@[expose] noncomputable def tvK (m : Nat) : Bool :=
  anyL (List.range 16) fun u => andB (notB (bitK m u))
    (allL (List.range 16) fun y => orB (bitK m y) (bitK m (Nat.xor u y)))

end CFSG.KC.LQT.Syl

end
