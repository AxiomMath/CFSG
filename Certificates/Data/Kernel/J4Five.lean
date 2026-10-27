module

public import Certificates.Data.Kernel.J4Count
public import Certificates.Data.Kernel.J4Q.Mat

public section

namespace CFSG.KC.J4Five

open CFSG.KC.J4Count CFSG.KC.J4Q CFSG.KC.Loop

@[expose] noncomputable def all64 (hi : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun h ih => andB (Nat.rec (motive := fun _ => Bool) true
      (fun l ih2 => andB (f (Nat.add (Nat.mul (nat_lit 64) h) l)) ih2) (nat_lit 64)) ih) hi

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def imgN (f : Nat → Nat) (m : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.shiftLeft (nat_lit 1) (f i))
        (Nat.testBit m i))) n

@[expose] noncomputable def imgF (f : Nat → Nat) (m : Nat) : Nat := imgN f m (nat_lit 24)

@[expose] noncomputable def inC (B P : List Nat) (a : Nat) : Bool :=
  Nat.beq (combo B (decode P a)) a

@[expose] noncomputable def pcN (m n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight m i) (nat_lit 1))) n

@[expose] noncomputable def zPow (z : List Nat) (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => getN 0 z y) k

@[expose] noncomputable def maskL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) x) ih) L

@[expose] noncomputable def genOK (B P : List Nat) (f : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => andB (inC B P (imgF f b)) ih) B

@[expose] noncomputable def invOK (B P : List Nat) : Bool :=
  all64 (nat_lit 64) fun s => Nat.beq (decode P (combo B s)) s

@[expose] noncomputable def isOct5 (z : List Nat) (Fm Tm a : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun j acc => orB (Nat.beq a (Nat.lor Fm (imgF (zPow z j) Tm))) acc) (nat_lit 5)

@[expose] noncomputable def octOK (B z : List Nat) (Fm Tm : Nat) : Bool :=
  all64 (nat_lit 64) fun s => strictB (combo B s) fun a =>
    orB (notB (andB (Nat.beq (pcN a (nat_lit 24)) (nat_lit 8)) (Nat.beq (Nat.land a Fm) Fm)))
      (isOct5 z Fm Tm a)

@[expose] def perms4 (L : List Nat) : List (List Nat) :=
  L.flatMap fun a => (L.filter (· != a)).flatMap fun b =>
    ((L.filter (· != a)).filter (· != b)).flatMap fun c =>
      (((L.filter (· != a)).filter (· != b)).filter (· != c)).map fun d => [a, b, c, d]

@[expose] def cands (Fl Tl : List Nat) : List (List Nat) :=
  (perms4 Fl).flatMap fun a => (perms4 Tl).map fun b => a ++ b

@[expose] noncomputable def distB (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x t ih => andB (List.rec (motive := fun _ => Bool) true
      (fun y _ ih2 => andB (notB (Nat.beq x y)) ih2) t) ih) l

@[expose] noncomputable def bld (z crd c : List Nat) (x : Nat) : Nat :=
  zPow z (Nat.div (getN 0 crd x) (nat_lit 8)) (getN 0 c (Nat.mod (getN 0 crd x) (nat_lit 8)))

@[expose] noncomputable def candN (B P z crd Fl Tl : List Nat) : Nat :=
  ((cands Fl Tl).filter fun c => genOK B P (bld z crd c)).length

@[expose] noncomputable def crdOK (z crd L : List Nat) : Bool :=
  allN (nat_lit 24) fun x => andB (Nat.blt (Nat.mod (getN 0 crd x) (nat_lit 8)) (nat_lit 8))
    (Nat.beq (zPow z (Nat.div (getN 0 crd x) (nat_lit 8))
      (getN 0 L (Nat.mod (getN 0 crd x) (nat_lit 8)))) x)

@[expose] noncomputable def fixOK (z Fl : List Nat) : Bool :=
  allN (nat_lit 24) fun x => andB (Nat.blt (getN 0 z x) (nat_lit 24))
    (Bool.rec (motive := fun _ => Bool) (notB (List.elem x Fl)) (List.elem x Fl)
      (Nat.beq (getN 0 z x) x))

@[expose] noncomputable def sqOK (T0 T1 T2 Y Z : List Nat) : Bool :=
  allN (nat_lit 24) fun x => andB (Nat.beq (getN 0 Y (getN 0 T2 x)) (getN 0 T0 (getN 0 T1 x)))
    (Nat.beq (getN 0 Z x) (getN 0 Y (getN 0 Y x)))

@[expose] noncomputable def idxK (v : Nat) (P : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Bool.rec (motive := fun _ => Nat) (Nat.succ ih) (nat_lit 0) (Nat.beq v x)) P

@[expose] noncomputable def eqvOK (rm one : Nat) (P G PHI : List Nat) (n g : Nat) : Bool :=
  allN g fun l => allN n fun i =>
    strictB (idxK (vecJ rm (getN 0 P i) (getN one G l)) P) fun j =>
      andB (Nat.blt j n)
        (Nat.beq (vecJ rm (getN 0 P (getN 0 PHI i)) (getN one G l)) (getN 0 P (getN 0 PHI j)))

@[expose] noncomputable def vwK (rm one : Nat) (mats invs : List Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (vecJ rm x (letJ one mats invs l)) ih) w

@[expose] def GB : List Nat :=
  [975, 15600, 22947, 38236, 67957, 132534, 266429, 531598, 1054811, 2102375, 4197785, 8392042]

@[expose] def GP : List Nat := [9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] def YT : List Nat :=
  [9, 2, 17, 12, 20, 15, 11, 22, 19, 23, 14, 8, 7, 18, 10, 6, 13, 0, 21, 3, 4, 1, 5, 16]

@[expose] def XI : List Nat :=
  [23, 17, 0, 7, 4, 6, 8, 5, 3, 16, 10, 19, 22, 21, 14, 11, 18, 9, 1, 12, 20, 2, 15, 13]

@[expose] def FL : List Nat := [4, 10, 14, 20]

@[expose] def TL : List Nat := [0, 3, 15, 18]

@[expose] def CRD : List Nat :=
  [4, 15, 36, 5, 0, 21, 29, 13, 37, 31, 1, 14, 30, 20, 2, 6, 39, 23, 7, 22, 3, 28, 38, 12]

@[expose] def PHI : List Nat := [1, 0, 4, 5, 2, 3, 7, 6, 11, 10, 9, 8, 13, 12]

end CFSG.KC.J4Five

end
