module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.Kernel.SporSch.J4SPairK

public section

namespace CFSG.KC.J4Slp

open CFSG.KC.J4Q CFSG.KC.Loop

@[expose] noncomputable def setN (l : List Nat) (i x : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun m t ih i => Nat.rec (motive := fun _ => List Nat) (List.cons x t)
      (fun j _ => List.cons m (ih j)) i) l i

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def forceL (l : List Nat) (k : List Nat → List Nat) : List Nat :=
  List.rec (motive := fun _ => (List Nat → List Nat) → List Nat) (fun k => k List.nil)
    (fun x _ ih k => strictL x fun a => ih fun t => k (List.cons a t)) l k

@[expose] noncomputable def regM (R : List Nat) (r : Nat) : Nat := getN 0 R (Nat.mul 2 r)

@[expose] noncomputable def regI (R : List Nat) (r : Nat) : Nat :=
  getN 0 R (Nat.add (Nat.mul 2 r) 1)

@[expose] noncomputable def setR (R : List Nat) (k x y : Nat) : List Nat :=
  setN (setN R (Nat.mul 2 k) x) (Nat.add (Nat.mul 2 k) 1) y

@[expose] noncomputable def stepK (c rm one : Nat) (R : List Nat) (code : List Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    (Bool.rec (motive := fun _ => List Nat)
      (setR R (getN 0 code 3) (powJ c rm one (regM R (getN 0 code 2)) (getN 0 code 1))
        (powJ c rm one (regI R (getN 0 code 2)) (getN 0 code 1)))
      (setR R (getN 0 code 2) (regI R (getN 0 code 1)) (regM R (getN 0 code 1)))
      (Nat.beq (getN 0 code 0) 1))
    (setR R (getN 0 code 3) (mulJ c rm (regM R (getN 0 code 1)) (regM R (getN 0 code 2)))
      (mulJ c rm (regI R (getN 0 code 2)) (regI R (getN 0 code 1))))
    (Nat.beq (getN 0 code 0) 0)

@[expose] noncomputable def runK (c rm one : Nat) (prog : List (List Nat)) (R : List Nat) :
    List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun R => R)
    (fun code _ ih R => forceL (stepK c rm one R code) ih) prog R

@[expose] def initK (one A Ai B Bi : Nat) : List Nat :=
  [one, one, A, Ai, B, Bi, one, one, one, one, one, one, one, one]

@[expose] def max7Codes : List (List Nat) := [
  [0, 1, 2, 3], [0, 3, 2, 4], [0, 3, 4, 5], [0, 3, 5, 6], [0, 6, 4, 5], [2, 4, 4, 3],
  [2, 8, 5, 4], [1, 4, 5], [0, 5, 3, 6], [0, 6, 4, 3], [0, 1, 3, 4], [0, 4, 3, 5], [2, 3, 5, 6],
  [0, 4, 4, 5], [0, 6, 5, 3], [2, 6, 4, 5], [0, 5, 3, 4], [2, 20, 4, 3], [0, 3, 2, 5],
  [0, 2, 3, 6], [1, 6, 3], [0, 3, 5, 6], [2, 3, 6, 2], [0, 4, 2, 3], [0, 4, 3, 5], [2, 7, 5, 3],
  [1, 4, 5], [0, 5, 2, 6], [0, 2, 6, 5], [2, 8, 4, 2], [0, 2, 5, 6], [1, 6, 5], [0, 1, 4, 2],
  [0, 5, 3, 4], [0, 4, 6, 1]]

@[expose] noncomputable def chk11 (c rm one p : Nat) (R : List Nat) : Bool :=
  strictB (regM R 1) fun h1 => strictB (regI R 1) fun h1i =>
  strictB (regM R 2) fun h2 => strictB (regI R 2) fun h2i =>
  strictB (powJ c rm one h2 8) fun s => strictB (powJ c rm one h2i 8) fun si =>
  strictB (mulJ c rm s h1i) fun t1 => strictB (mulJ c rm h1 si) fun t1i =>
  strictB (mulJ c rm t1 si) fun t2 => strictB (mulJ c rm s t1i) fun t2i =>
  strictB (mulJ c rm t2 h1) fun x0 => strictB (mulJ c rm h1i t2i) fun x0i =>
  strictB (mulJ c rm h1 h2) fun u => strictB (mulJ c rm h2i h1i) fun ui =>
  strictB (mulJ c rm s u) fun c1 => strictB (mulJ c rm ui si) fun c1i =>
  strictB (mulJ c rm c1 si) fun c2 => strictB (mulJ c rm s c1i) fun c2i =>
  strictB (mulJ c rm c2 ui) fun y0 => strictB (mulJ c rm u c2i) fun y0i =>
  strictB (powJ c rm one y0 7) fun y7 => strictB (powJ c rm one y0i 7) fun y7i =>
  strictB (mulJ c rm x0 y7) fun qx => strictB (mulJ c rm y7i x0i) fun qxi =>
  strictB (powJ c rm one y0 3) fun qy => strictB (powJ c rm one y0i 3) fun qyi =>
  andB (Nat.beq (vecJ rm p qx) p)
    (notB (Nat.beq (Nat.mod (vecJ rm (vecJ rm (vecJ rm (vecJ rm p qx) qy) qxi) qyi)
      (Nat.pow 2 112)) p))

@[expose] def wordP1 : List Int := [1, -2, 1, 2, 1, 2, 1, -2, -1, -2, -1, -2, -2, -1, 2, -1, 2, -1,
  2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1]

end CFSG.KC.J4Slp

end
