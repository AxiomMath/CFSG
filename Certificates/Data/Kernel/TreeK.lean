module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.TreeK

open CFSG.KLie.CT

@[expose] noncomputable def spanLt (x : Nat) (ys : List Nat) (k : List Nat → List Nat → List Nat) :
    List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => k (List.reverse acc) [])
    (fun y ys' ih acc => Bool.rec (motive := fun _ => List Nat) (k (List.reverse acc) (List.cons y ys'))
      (ih (List.cons y acc)) (Nat.blt y x)) ys

@[expose] noncomputable def mergeK (xs : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun ys => ys)
    (fun x _ ih ys => spanLt x ys (fun p r => List.append p (List.cons x (ih r))) []) xs

@[expose] noncomputable def passK (rs : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => Option (List Nat) → List (List Nat))
    (fun o => Option.rec (motive := fun _ => List (List Nat)) [] (fun a => [a]) o)
    (fun r _ ih o => Option.rec (motive := fun _ => List (List Nat)) (ih (some r))
      (fun a => List.cons (mergeK a r) (ih none)) o) rs none

@[expose] noncomputable def sincK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Option Nat → Bool) (fun _ => true)
    (fun x _ ih o => andB (Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o)
      (ih (some x))) l none

@[expose] noncomputable def popQ (F B : List Nat) : List Nat × List Nat :=
  List.rec (motive := fun _ => List Nat × List Nat) (Prod.mk List.nil List.nil)
    (fun _ F' _ => List.rec (motive := fun _ => List Nat × List Nat) (Prod.mk (List.reverse B) List.nil)
      (fun _ _ _ => Prod.mk F' B) F') F

@[expose] noncomputable def popsQ (k : Nat) (F B : List Nat) : List Nat × List Nat :=
  Nat.rec (motive := fun _ => List Nat × List Nat) (Prod.mk F B)
    (fun _ ih => Prod.rec (motive := fun _ => List Nat × List Nat) (fun F B => popQ F B) ih) k

@[expose] noncomputable def headQ (F : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ _ => x) F

@[expose] noncomputable def pushQ (y : Nat) (F B : List Nat) : List Nat × List Nat :=
  List.rec (motive := fun _ => List Nat × List Nat) (Prod.mk (List.cons y List.nil) List.nil)
    (fun _ _ _ => Prod.mk F (List.cons y B)) F

@[expose] noncomputable def walkK (act : Nat → Nat → Nat) (ng : Nat) :
    List (Nat × Nat) → Nat → Nat → List Nat → List Nat → List Nat → List Nat × Bool :=
  List.rec (motive := fun _ => Nat → Nat → List Nat → List Nat → List Nat → List Nat × Bool)
    (fun _ _ _ _ acc => Prod.mk acc true)
    (fun r _ ih h n F B acc => Prod.rec (motive := fun _ => List Nat × Bool) (fun p l =>
      Bool.rec (motive := fun _ => List Nat × Bool) (Prod.mk acc false)
        (Prod.rec (motive := fun _ => List Nat × Bool) (fun F B =>
          (fun y => Prod.rec (motive := fun _ => List Nat × Bool)
            (fun F B => ih p (Nat.succ n) F B (List.cons y acc)) (pushQ y F B))
            (act l (headQ F))) (popsQ (Nat.sub p h) F B))
        (andB (Nat.ble h p) (andB (Nat.blt p n) (Nat.blt l ng)))) r)

@[expose] noncomputable def treePts (act : Nat → Nat → Nat) (ng root : Nat) (recs : List (Nat × Nat)) :
    List Nat × Bool :=
  Prod.rec (motive := fun _ => List Nat × Bool) (fun acc ok => Prod.mk (List.reverse acc) ok)
    (walkK act ng recs (nat_lit 0) (nat_lit 1) (List.cons root List.nil) List.nil
      (List.cons root List.nil))

@[expose] noncomputable def sortP (np : Nat) (xs : List Nat) : List Nat :=
  List.flatten (Nat.rec (motive := fun _ => List (List Nat)) (List.map (fun x => [x]) xs)
    (fun _ ih => passK ih) np)

@[expose] noncomputable def distinctK (np : Nat) (xs : List Nat) : Bool := sincK (sortP np xs)

@[expose] noncomputable def subS (xs : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun x _ ih ys => List.rec (motive := fun _ => Bool) false
      (fun y ys' ihy => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false ihy (Nat.blt y x))
        (ih (List.cons y ys')) (Nat.beq x y)) ys) xs

@[expose] noncomputable def imagesK (act : Nat → Nat → Nat) (ng : Nat) (xs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x _ ih => Nat.rec (motive := fun _ => List Nat) ih (fun l acc => List.cons (act l x) acc) ng) xs

@[expose] noncomputable def closedK (act : Nat → Nat → Nat) (ng np : Nat) (xs : List Nat) : Bool :=
  (fun S => andB (sincK S) (subS (sortP np (imagesK act ng xs)) S)) (sortP np xs)

@[expose] noncomputable def treeOK (act : Nat → Nat → Nat) (ng np root : Nat) (recs : List (Nat × Nat)) :
    Bool :=
  Prod.rec (motive := fun _ => Bool) (fun xs ok => andB ok (distinctK np xs)) (treePts act ng root recs)

end CFSG.KC.TreeK

end
