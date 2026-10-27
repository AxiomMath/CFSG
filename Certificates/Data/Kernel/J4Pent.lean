module

public import Certificates.Data.Kernel.J4Q.Mat

public section

namespace CFSG.KC.J4Pent

open CFSG.KC.Loop CFSG.KC.J4Q

@[expose] noncomputable def nthL {α : Type} (d : α) (l : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) l i

@[expose] noncomputable def dropK {α : Type} (n : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l)
    (fun _ ih l => List.rec (motive := fun _ => List α) List.nil (fun _ t _ => ih t) l) n l

@[expose] noncomputable def takeK {α : Type} (n : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun _ => List.nil)
    (fun _ ih l => List.rec (motive := fun _ => List α) List.nil (fun x t _ => List.cons x (ih t)) l)
    n l

@[expose] noncomputable def mapS (f : Nat → Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun x _ ih => List.cons (f x) ih) l

@[expose] noncomputable def zipS (f : Nat → Nat → Nat) (A B : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => List.nil)
    (fun a _ ih B => List.rec (motive := fun _ => List Nat) List.nil
      (fun b bs _ => List.cons (f a b) (ih bs)) B) A B

@[expose] noncomputable def eqL (A B : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun B => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) B)
    (fun a _ ih B => List.rec (motive := fun _ => Bool) false (fun b bs _ => bAnd(Nat.beq a b, ih bs)) B)
    A B

@[expose] noncomputable def allB {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(p x, ih)) l

@[expose] noncomputable def anyB {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(p x, true, ih)) l

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => strictN ih fun n => Nat.succ n) l

@[expose] noncomputable def allLt (b n : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun n => Nat.beq n 0)
    (fun x _ ih n => bAnd(Nat.blt x b, Nat.rec (motive := fun _ => Bool) false (fun m _ => ih m) n))
    l n

abbrev T2 := Nat × Nat
abbrev T4 := T2 × T2
abbrev T8 := T4 × T4
abbrev T16 := T8 × T8

@[expose] noncomputable def tr4 (b0 b1 b2 b3 : Nat) : T16 :=
  (fun x1 x2 x4 x8 =>
    (fun x3 x5 x6 x9 x10 x12 =>
      (fun x7 x11 x13 x14 =>
        ((((0, x1), (x2, x3)), ((x4, x5), (x6, x7))),
          (((x8, x9), (x10, x11)), ((x12, x13), (x14, Nat.xor x14 x1)))))
      (Nat.xor x6 x1) (Nat.xor x10 x1) (Nat.xor x12 x1) (Nat.xor x12 x2))
    (Nat.xor x1 x2) (Nat.xor x1 x4) (Nat.xor x2 x4) (Nat.xor x1 x8) (Nat.xor x2 x8) (Nat.xor x4 x8))
  b0 b1 b2 b3

@[expose] noncomputable def bitK (c k : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight c k) 1) 1

@[expose] noncomputable def selT (T : T16) (c : Nat) : Nat :=
  (fun t8 => (fun t4 => (fun t2 => Bool.rec (motive := fun _ => Nat) t2.1 t2.2 (bitK c 0))
      (Bool.rec (motive := fun _ => T2) t4.1 t4.2 (bitK c 1)))
    (Bool.rec (motive := fun _ => T4) t8.1 t8.2 (bitK c 2)))
  (Bool.rec (motive := fun _ => T8) T.1 T.2 (bitK c 3))

@[expose] noncomputable def tabsT (B : List Nat) (n : Nat) : List T16 :=
  Nat.rec (motive := fun _ => List Nat → List T16) (fun _ => List.nil)
    (fun _ ih B => List.cons (tr4 (nthL 0 B 0) (nthL 0 B 1) (nthL 0 B 2) (nthL 0 B 3))
      (ih (dropK 4 B))) n B

@[expose] noncomputable def dotT (Ts : List T16) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun T _ ih c acc => strictN acc fun a => ih (Nat.shiftRight c 4) (Nat.xor a (selT T c)))
    Ts c 0

@[expose] noncomputable def appT (MT : Nat) (Ts : List T16) (lo n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih j => List.cons (dotT Ts (rowJ (nat_lit 5192296858534827628530496329220095) MT j))
      (ih (Nat.succ j))) n lo

@[expose] noncomputable def tab4 (W b0 b1 b2 b3 : Nat) : Nat :=
  (fun x1 x2 x4 x8 =>
    (fun x3 x5 x6 x9 x10 x12 =>
      (fun x7 x11 x13 x14 => Nat.shiftLeft (
        Nat.lor x1 (Nat.lor (Nat.shiftLeft x2 W) (Nat.lor (Nat.shiftLeft x3 (Nat.mul 2 W))
        (Nat.lor (Nat.shiftLeft x4 (Nat.mul 3 W)) (Nat.lor (Nat.shiftLeft x5 (Nat.mul 4 W))
        (Nat.lor (Nat.shiftLeft x6 (Nat.mul 5 W)) (Nat.lor (Nat.shiftLeft x7 (Nat.mul 6 W))
        (Nat.lor (Nat.shiftLeft x8 (Nat.mul 7 W)) (Nat.lor (Nat.shiftLeft x9 (Nat.mul 8 W))
        (Nat.lor (Nat.shiftLeft x10 (Nat.mul 9 W)) (Nat.lor (Nat.shiftLeft x11 (Nat.mul 10 W))
        (Nat.lor (Nat.shiftLeft x12 (Nat.mul 11 W)) (Nat.lor (Nat.shiftLeft x13 (Nat.mul 12 W))
        (Nat.lor (Nat.shiftLeft x14 (Nat.mul 13 W))
          (Nat.shiftLeft (Nat.xor x14 x1) (Nat.mul 14 W)))))))))))))))) W)
      (Nat.xor x6 x1) (Nat.xor x10 x1) (Nat.xor x12 x1) (Nat.xor x12 x2))
    (Nat.xor x1 x2) (Nat.xor x1 x4) (Nat.xor x2 x4) (Nat.xor x1 x8) (Nat.xor x2 x8) (Nat.xor x4 x8))
  b0 b1 b2 b3

@[expose] noncomputable def tabsW (W : Nat) (B : List Nat) (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun _ => List.nil)
    (fun _ ih B => List.cons (tab4 W (nthL 0 B 0) (nthL 0 B 1) (nthL 0 B 2) (nthL 0 B 3))
      (ih (dropK 4 B))) n B

@[expose] noncomputable def dotW (W ones : Nat) (Ts : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun T _ ih c acc => strictN acc fun a =>
      ih (Nat.shiftRight c 4)
        (Nat.xor a (Nat.land (Nat.shiftRight T (Nat.mul (Nat.land c 15) W)) ones)))
    Ts c 0

@[expose] noncomputable def appW (W ones MT : Nat) (Ts : List Nat) (lo n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih j => List.cons
      (dotW W ones Ts (rowJ (nat_lit 5192296858534827628530496329220095) MT j)) (ih (Nat.succ j)))
    n lo

@[expose] noncomputable def cmpS (ones : Nat) (A : List Nat) : List Nat → Nat × Nat :=
  List.rec (motive := fun _ => List Nat → Nat × Nat) (fun _ => (0, ones))
    (fun a _ ih B => List.rec (motive := fun _ => Nat × Nat) (0, ones)
      (fun b bs _ => Prod.rec (motive := fun _ => Nat × Nat) (fun lt eq =>
          (Nat.lor lt (Nat.land eq (Nat.land (Nat.xor a ones) b)),
            Nat.land eq (Nat.xor (Nat.xor a b) ones)))
        (ih bs)) B) A

@[expose] noncomputable def maskOf (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun l _ ih => strictN ih fun r => Nat.lor r (Nat.shiftLeft 1 l)) L

@[expose] noncomputable def laneV (B : List Nat) (l : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b _ ih j => strictN (ih (Nat.succ j)) fun r =>
      Nat.lor r (Nat.shiftLeft (Nat.land (Nat.shiftRight b l) 1) j)) B 0

@[expose] noncomputable def bcast (ones v : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih j => List.cons (nIf(Nat.beq (Nat.land (Nat.shiftRight v j) 1) 1, ones, 0))
      (ih (Nat.succ j))) 112 0

@[expose] noncomputable def canonAt (W ones n : Nat) (Ts Rt : List Nat) (MT tie : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool)
    (fun lt eq => bAnd(Nat.beq (Nat.lor lt eq) ones, Nat.beq eq tie))
    (cmpS ones Rt (appW W ones MT Ts (Nat.sub 112 n) n))

@[expose] noncomputable def incrS (ones : Nat) (R : List Nat) : Bool :=
  (fun m => Prod.rec (motive := fun _ => Bool) (fun lt _ => Nat.beq (Nat.land lt m) m)
      (cmpS ones R (mapS (fun x => Nat.shiftRight x 1) R)))
  (Nat.shiftRight ones 1)

@[expose] noncomputable def stepT (ones AT BT CT mA mB mC : Nat) (Y : List Nat) : List Nat :=
  (fun Ts => (fun m0 => zipS (fun y abc => Nat.lor (Nat.land y m0) abc) Y
      (zipS Nat.lor (zipS (fun a b => Nat.lor (Nat.land a mA) (Nat.land b mB))
        (appT AT Ts 0 112) (appT BT Ts 0 112))
        (mapS (fun c => Nat.land c mC) (appT CT Ts 0 112))))
    (Nat.xor ones (Nat.lor mA (Nat.lor mB mC))))
  (tabsT Y 28)

@[expose] noncomputable def walkT (ones AT BT CT : Nat) (S : List (Nat × Nat × Nat))
    (Y : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun Y => Y)
    (fun s _ ih Y => Prod.rec (motive := fun _ => List Nat)
      (fun a bc => Prod.rec (motive := fun _ => List Nat)
        (fun b c => ih (stepT ones AT BT CT a b c Y)) bc) s) S Y

@[expose] noncomputable def appendK {α : Type} (L L' : List α) : List α :=
  List.rec (motive := fun _ => List α) L' (fun x _ ih => List.cons x ih) L

@[expose] noncomputable def subsT (Ms : List Nat) (j0 n : Nat) (Y : List Nat) : List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat)) [Y]
    (fun k L => appendK L (List.rec (motive := fun _ => List (List Nat)) List.nil
      (fun X _ ih => List.cons (appT (nthL 0 Ms (Nat.add j0 k)) (tabsT X 28) 0 112) ih) L)) n

@[expose] noncomputable def agree4 (W one1 ones4 h : Nat) (A B : List Nat) : Nat :=
  (fun e => Nat.land one1 (Nat.land (Nat.land e (Nat.shiftRight e W))
      (Nat.land (Nat.shiftRight e (Nat.mul 2 W)) (Nat.shiftRight e (Nat.mul 3 W)))))
  (Nat.xor ones4 (List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun a _ ih B => List.rec (motive := fun _ => Nat) 0
      (fun b bs _ => strictN (ih bs) fun r => Nat.lor r (Nat.xor a b)) B) (takeK h A) B))

@[expose] noncomputable def anyAgree (W one1 ones4 h : Nat) (As Bs : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun A _ ih => strictN ih fun r => List.rec (motive := fun _ => Nat) r
      (fun B _ ih2 => strictN ih2 fun r2 => Nat.lor r2 (agree4 W one1 ones4 h A B)) Bs) As

@[expose] noncomputable def pairFlags (W one1 ones4 h : Nat) (As Bs : List (List Nat)) : Nat :=
  Nat.lor (anyAgree W one1 ones4 h (takeK 1 As) (dropK 1 Bs))
    (anyAgree W one1 ones4 h (dropK 1 As) Bs)

end CFSG.KC.J4Pent

end
