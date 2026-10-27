module

public import Certificates.Data.Kernel.Misc.O73

public section

namespace CFSG.KC.Misc.T46

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73

@[expose] noncomputable def f4K (x y : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.mul (Nat.mod x 2) (Nat.mod y 2)) (Nat.mul (Nat.div x 2)
      (Nat.div y 2))) 2)
    (Nat.mul 2 (Nat.mod (Nat.add (Nat.add (Nat.mul (Nat.mod x 2) (Nat.div y 2))
      (Nat.mul (Nat.div x 2) (Nat.mod y 2))) (Nat.mul (Nat.div x 2) (Nat.div y 2))) 2))

@[expose] noncomputable def crdK (c i : Nat) : Nat := Nat.mod (Nat.div c (Nat.pow 4 i)) 4

@[expose] noncomputable def hermK (c d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.xor acc
    (f4K (crdK c i) (letN (crdK d i) fun e => f4K e e))) 6

@[expose] noncomputable def scaleK (a c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc
    (Nat.mul (f4K a (crdK c i)) (Nat.pow 4 i))) 6

@[expose] noncomputable def leadK (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => letN (crdK c (Nat.sub 5 j)) fun e =>
    Bool.rec (motive := fun _ => Nat) e acc (Nat.beq e 0)) 6

@[expose] noncomputable def normK (c : Nat) : Nat := letN (leadK c) fun a => scaleK (f4K a a) c

@[expose] noncomputable def tvK (v x : Nat) : Nat := Nat.xor x (scaleK (hermK x v) v)

@[expose] noncomputable def weightK (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc
    (Bool.rec (motive := fun _ => Nat) 1 0 (Nat.beq (crdK c i) 0))) 6

@[expose] noncomputable def gensK (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [85] (fun c _ ih => Bool.rec (motive := fun _ => List Nat)
    ih (List.cons c ih) (Nat.beq (weightK c) 2)) l

@[expose] noncomputable def fmtW (cs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun st => notB (Nat.beq st 1))
    (fun c _ ih st => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (andB (Nat.ble 48 c) (Nat.ble c 57)) (ih 2))
        (andB (Nat.beq st 0) (ih 1)) (Nat.beq c 45))
      (andB (notB (Nat.beq st 1)) (ih 0)) (Nat.beq c 32)) cs 0

@[expose] noncomputable def intsK (cs : List Nat) : List Int :=
  List.rec (motive := fun _ => Nat → Bool → List Int)
    (fun cur ng => Bool.rec (motive := fun _ => List Int) [tok cur ng] [] (Nat.beq cur 0))
    (fun c _ ih cur ng => Bool.rec (motive := fun _ => List Int)
      (Bool.rec (motive := fun _ => List Int)
        (ih (Nat.succ (Nat.add (Nat.mul 10 (Nat.pred cur)) (Nat.sub c 48))) ng) (ih cur true)
        (Nat.beq c 45))
      (Bool.rec (motive := fun _ => List Int) (List.cons (tok cur ng) (ih 0 false)) (ih 0 false)
        (Nat.beq cur 0))
      (Nat.beq c 32)) cs 0 false
where
  tok (cur : Nat) (ng : Bool) : Int :=
    Bool.rec (motive := fun _ => Int) (Int.ofNat (Nat.pred cur)) (Int.neg (Int.ofNat (Nat.pred cur)))
      ng

@[expose] noncomputable def wordG (G : List Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (idP 693 10)
    (fun z _ ih => compP 693 10 (wordM7.nthN G (Nat.sub (Int.natAbs z) 1)) ih) w

@[expose] noncomputable def lettersOK (m : Nat) (w : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih =>
    andB (andB (Nat.ble 1 (Int.natAbs z)) (Nat.ble (Int.natAbs z) m)) ih) w

@[expose] noncomputable def wordXY (X Y : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (idP 693 10)
    (fun z _ ih => compP 693 10 (Bool.rec (motive := fun _ => Nat) Y X (Nat.beq z 1)) ih) w

@[expose] noncomputable def powP (e P : Nat) : Nat :=
  letN P fun P => Nat.rec (motive := fun _ => Nat) (idP 693 10) (fun _ acc => compP 693 10 P acc) e

@[expose] noncomputable def ptsK (UL : List Nat) (UP : Nat) : Bool :=
  andB (Nat.beq (lenN UL) 693) <| andB (Nat.blt UP (Nat.shiftLeft 1 (Nat.mul 12 693))) <|
  andB (allN 693 fun i => Nat.beq (at' 12 UP i) (wordM7.nthN UL i)) <|
  andB (allN 692 fun i => Nat.blt (at' 12 UP i) (at' 12 UP (Nat.succ i))) <|
    allN 693 fun x => letB (at' 12 UP x) fun c => Nat.beq (normK (tvK 0 c)) c

@[expose] noncomputable def genK (UP v G : Nat) : Bool :=
  letB G fun G => andB (permK 693 10 G) <| allN 693 fun x =>
    letB (normK (tvK v (at' 12 UP x))) fun d => letB (at' 10 G x) fun j =>
      andB (Nat.blt j 693) (Nat.beq (at' 12 UP j) d)

@[expose] noncomputable def gensOK (UL : List Nat) (UP : Nat) (GP : List Nat) (lo n : Nat) : Bool :=
  andB (Nat.beq (lenN (gensK UL)) 46) <| andB (Nat.beq (lenN GP) 46) <|
    allN n fun d => letB (Nat.add lo d) fun k => impB (Nat.blt k 46)
      (genK UP (wordM7.nthN (gensK UL) k) (wordM7.nthN GP k))

@[expose] noncomputable def lettersK (GP : List Nat) (WC : List (List Nat)) (LP : List Nat) :
    Bool :=
  andB (Nat.beq (relPK.lenLLN WC) 53) <| andB (Nat.beq (lenN LP) 106) <|
  andB (allLL WC fmtW) <|
  andB (allN 46 fun k => decide (intsK (nthL WC k) = [Int.ofNat (Nat.succ k)])) <|
    allN 53 fun j => letB (wordM7.nthN LP (Nat.mul 2 j)) fun A =>
      letB (wordM7.nthN LP (Nat.succ (Nat.mul 2 j))) fun B =>
      andB (lettersOK 46 (intsK (nthL WC j))) <| andB (Nat.beq A (wordG GP (intsK (nthL WC j)))) <|
        andB (permK 693 10 B) (Nat.beq (compP 693 10 A B) (idP 693 10))

@[expose] noncomputable def lvK (LP : List Nat) (b : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun l acc => Bool.rec (motive := fun _ => List Nat) acc
    (List.cons l acc) (Nat.beq (at' 10 (wordM7.nthN LP l) b) b)) (lenN LP)

@[expose] noncomputable def orbK (LP lv : List Nat) (root m : Nat) (O Pa La : List Nat) : Bool :=
  letB (List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.lor ih (Nat.shiftLeft 1 p)) O)
    fun S => andB (Nat.beq (lenN O) m) <| andB (Nat.beq (lenN Pa) m) <|
    andB (Nat.beq (lenN La) m) <| andB (allL O fun p => Nat.blt p 693) <|
    andB (Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.add ih (Nat.shiftLeft 1 p)) O)
      S) <|
    andB (Nat.beq (wordM7.nthN O 0) root) <|
    andB (allN m fun i => impB (Nat.blt 0 i) (letB (wordM7.nthN Pa i) fun a =>
      letB (wordM7.nthN La i) fun l => andB (Nat.blt a i) <| andB (memN l lv) <|
        Nat.beq (at' 10 (wordM7.nthN LP l) (wordM7.nthN O a)) (wordM7.nthN O i))) <|
    allL lv fun l => letB (wordM7.nthN LP l) fun L =>
      allL O fun p => Nat.beq (Nat.land (Nat.shiftRight S (at' 10 L p)) 1) 1

@[expose] noncomputable def treesK (LP : List Nat) (BL : List Nat) (r : Nat)
    (O1 Pa1 La1 O2 Pa2 La2 : List Nat) : Bool :=
  letLN' (lvK LP (wordM7.nthN BL 0)) fun lv =>
  andB (Nat.beq (lenN BL) 5) <|
  andB (orbK LP lv (wordM7.nthN BL 1) 512 O1 Pa1 La1) <| andB (orbK LP lv r 180 O2 Pa2 La2) <|
    letB (List.rec (motive := fun _ => Nat) 1 (fun p _ ih => Nat.lor ih (Nat.shiftLeft 1 p))
      (List.append O1 O2)) fun S => Nat.beq S (Nat.sub (Nat.shiftLeft 1 693) 1)
where
  letLN' (l : List Nat) (k : List Nat → Bool) : Bool :=
    List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc.reverse)
      (fun x _ ih acc => letB x fun x => ih (List.cons x acc)) l []

@[expose] noncomputable def xyK (GP : List Nat) (xw yw : List Int) : Bool :=
  andB (lettersOK 46 xw) <| andB (lettersOK 46 yw) <|
  letB (powP 3 (wordG GP xw)) fun X => letB (powP 2 (wordG GP yw)) fun Y =>
  letB (compP 693 10 X Y) fun Z =>
  andB (Nat.beq (powP 2 X) (idP 693 10)) <| andB (notB (Nat.beq X (idP 693 10))) <|
  andB (Nat.beq (powP 3 Y) (idP 693 10)) <| andB (notB (Nat.beq Y (idP 693 10))) <|
    andB (Nat.beq (powP 11 Z) (idP 693 10)) (notB (Nat.beq Z (idP 693 10)))

@[expose] noncomputable def tvWordsK (GP : List Nat) (xw yw : List Int) (TW : List (List Nat))
    (lo n : Nat) : Bool :=
  andB (Nat.beq (relPK.lenLLN TW) 46) <|
  letB (powP 3 (wordG GP xw)) fun X => letB (powP 2 (wordG GP yw)) fun Y =>
    allN n fun d => letB (Nat.add lo d) fun k => impB (Nat.blt k 46)
      (Nat.beq (wordXY X Y (nthL TW k)) (wordM7.nthN GP k))

end CFSG.KC.Misc.T46

end
