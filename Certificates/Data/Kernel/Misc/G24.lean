module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.Misc.G24

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def letterK (c : Nat) : Nat :=
  letN (Bool.rec (motive := fun _ => Nat) c (Nat.sub c 32) (Nat.ble 97 c)) fun u =>
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) 6 5 (Nat.beq u 71))
    (Nat.sub u 65) (andB (Nat.ble 65 u) (Nat.ble u 69))

@[expose] noncomputable def lowerK (c : Nat) : Bool := andB (Nat.ble 97 c) (Nat.ble c 122)

@[expose] noncomputable def parseK (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun c _ ih => Bool.rec (motive := fun _ => List Nat)
      (List.cons (Nat.add (Nat.mul 2 (letterK c))
        (Bool.rec (motive := fun _ => Nat) 0 1 (lowerK c))) ih) ih (Nat.beq (letterK c) 6)) cs

@[expose] noncomputable def appN (a b : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) b (fun x _ ih => List.cons x ih) a

@[expose] noncomputable def invRevK (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun x _ ih acc => ih (List.cons (Nat.xor x 1) acc)) w List.nil

@[expose] noncomputable def commK (u v : List Nat) : List Nat :=
  appN u (appN v (appN (invRevK u) (invRevK v)))

@[expose] noncomputable def commsK (ps : List (List Nat × List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun p _ ih => appN (Prod.rec (motive := fun _ => List Nat)
      (fun u v => commK (parseK u) (parseK v)) p) ih) ps

@[expose] noncomputable def bit (x k : Nat) : Nat := Nat.land (Nat.shiftRight x k) (nat_lit 1)

@[expose] noncomputable def mulF2 (n A B : Nat) : Nat :=
  letN A fun A => letN B fun B => letN (Nat.sub (Nat.shiftLeft 1 n) 1) fun F =>
  letN (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul n n)) 1) F) fun R =>
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.xor acc (Nat.land
    (Nat.mul (Nat.land (Nat.shiftRight A k) R) F)
    (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul n k)) F) R))) n

@[expose] noncomputable def oneF2 (n : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul n (Nat.succ n))) 1)
    (Nat.sub (Nat.shiftLeft 1 (Nat.succ n)) 1)

@[expose] noncomputable def blowEntry (i j d : Nat) : Nat :=
  letN (Nat.land d 1) fun x₀ => letN (Nat.land (Nat.shiftRight d 1) 1) fun x₁ =>
  letN (Nat.add (Nat.mul 56 i) (Nat.mul 2 j)) fun p =>
  Nat.lor (Nat.lor (Nat.shiftLeft x₀ p) (Nat.shiftLeft x₁ (Nat.succ p)))
    (Nat.lor (Nat.shiftLeft x₁ (Nat.add p 28)) (Nat.shiftLeft (Nat.xor x₀ x₁) (Nat.add p 29)))

@[expose] noncomputable def blowRows (rs : List (List Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun r _ ih i acc => ih (Nat.succ i) (List.rec (motive := fun _ => Nat → Nat) (fun _ => acc)
      (fun d _ ih2 j => Nat.lor (blowEntry i j d) (ih2 (Nat.succ j))) r 0)) rs

@[expose] noncomputable def shape4 (rs : List (List Nat)) : Bool :=
  andB (Nat.beq (lenLLK rs) 14) (allLL rs fun r => andB (Nat.beq (lenN r) 14)
    (allL r fun d => Nat.blt d 4))
where
  lenLLK (L : List (List Nat)) : Nat :=
    List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def blow14 (rs : List (List Nat)) : Nat := blowRows rs 0 0

@[expose] noncomputable def asciiK (rs : List (List Nat)) : Bool :=
  allLL rs fun r => allL r fun c => Nat.blt c 128

@[expose] noncomputable def digitsOf (rs : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun r _ ih => List.cons (List.rec (motive := fun _ => List Nat) List.nil
      (fun c _ ih2 => List.cons (Nat.mod (Nat.sub c 48) 4) ih2) r) ih) rs

@[expose] noncomputable def nthV (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def nthL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) L i

@[expose] noncomputable def nthLL (L : List (List (List Nat))) (i : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List (List Nat)) x (fun j _ => ih j) i) L i

@[expose] noncomputable def nthP (L : List (List (List Nat × List Nat))) (i : Nat) :
    List (List Nat × List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat × List Nat)) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List (List Nat × List Nat)) x (fun j _ => ih j) i)
    L i

@[expose] noncomputable def wordF4 (Gb w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (oneF2 28)
    (fun l _ ih => mulF2 28 (nthV Gb (Nat.div l 2)) ih) w

@[expose] noncomputable def g24F4K (GR : List (List (List Nat))) (Gb : List Nat)
    (RS : List (List Nat)) (PS : List (List (List Nat × List Nat)))
    (XS YS : List (List Nat)) (XL YL : List (List (List Nat))) : Bool :=
  andB (Nat.beq (lenN Gb) 6) <|
  andB (allN 6 fun i => andB (andB (asciiK (nthLL GR i)) (shape4 (digitsOf (nthLL GR i))))
    (Nat.beq (blow14 (digitsOf (nthLL GR i))) (nthV Gb i))) <|
  andB (allN 6 fun i => Nat.beq (mulF2 28 (nthV Gb i) (nthV Gb i)) (oneF2 28)) <|
  andB (allLL RS fun r => Nat.beq (wordF4 Gb (parseK r)) (oneF2 28)) <|
  andB (allN 6 fun i => Nat.beq (wordF4 Gb (commsK (nthP PS i))) (nthV Gb i)) <|
    allN 8 fun k => andB (andB (shape4 (nthLL XL k)) (shape4 (nthLL YL k)))
      (andB (Nat.beq (blow14 (nthLL XL k)) (wordF4 Gb (parseK (nthL XS k))))
        (Nat.beq (blow14 (nthLL YL k)) (wordF4 Gb (parseK (nthL YS k)))))

@[expose] noncomputable def laneOnes : Nat := Nat.div (Nat.sub (Nat.shiftLeft 1 1152) 1) 255

@[expose] noncomputable def colMask : Nat :=
  Nat.mul 255 (Nat.div (Nat.sub (Nat.shiftLeft 1 1152) 1) (Nat.sub (Nat.shiftLeft 1 96) 1))

@[expose] noncomputable def one3 : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 1248) 1) (Nat.sub (Nat.shiftLeft 1 104) 1)

@[expose] noncomputable def red3 (x : Nat) : Nat :=
  letN laneOnes fun L => letN (Nat.shiftLeft L 7) fun H =>
    csub 8 L H 3 (csub 8 L H 6 (csub 8 L H 12 (csub 8 L H 24 (csub 8 L H 48 x))))

@[expose] noncomputable def mulF3 (A B : Nat) : Nat :=
  letN A fun A => letN B fun B => letN colMask fun M =>
  red3 (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.add acc (Nat.mul
    (Nat.land (Nat.shiftRight A (Nat.mul 8 k)) M)
    (Nat.land (Nat.shiftRight B (Nat.mul 96 k)) (Nat.sub (Nat.shiftLeft 1 96) 1)))) 12)

@[expose] noncomputable def packRows3 (rs : List (List Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun r _ ih i acc => ih (Nat.succ i) (List.rec (motive := fun _ => Nat → Nat) (fun _ => acc)
      (fun d _ ih2 j => Nat.lor (Nat.shiftLeft d (Nat.mul 8 (Nat.add (Nat.mul 12 i) j)))
        (ih2 (Nat.succ j))) r 0)) rs

@[expose] noncomputable def res3Of (rs : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun r _ ih => List.cons (List.rec (motive := fun _ => List Nat) List.nil
      (fun c _ ih2 => List.cons (Nat.mod (Nat.sub c 48) 3) ih2) r) ih) rs

@[expose] noncomputable def shape12 (rs : List (List Nat)) : Bool :=
  andB (Nat.beq (shape4.lenLLK rs) 12) (allLL rs fun r => Nat.beq (lenN r) 12)

@[expose] noncomputable def word3 (Lb Lib w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one3
    (fun l _ ih => mulF3 (Bool.rec (motive := fun _ => Nat) (nthV Lib (Nat.div l 2))
      (nthV Lb (Nat.div l 2)) (Nat.beq (Nat.mod l 2) 1)) ih) w

@[expose] noncomputable def coverK (RS : List (List Nat)) (PS : List (List (List Nat × List Nat))) :
    List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat) → List (List Nat)) (fun acc => acc)
    (fun x _ ih acc => List.cons x (ih acc))
    (Nat.rec (motive := fun _ => List (List Nat)) List.nil (fun i acc =>
      List.rec (motive := fun _ => List (List Nat) → List (List Nat)) (fun a => a)
        (fun x _ ih a => List.cons x (ih a)) acc
        (List.rec (motive := fun _ => List (List Nat)) List.nil
          (fun r _ ih => List.cons (commK [Nat.add (Nat.mul 2 i) 1] (parseK r)) ih) RS)) 6)
    (Nat.rec (motive := fun _ => List (List Nat)) List.nil (fun i acc =>
      List.rec (motive := fun _ => List (List Nat) → List (List Nat)) (fun a => a)
        (fun x _ ih a => List.cons x (ih a)) acc
        [List.cons (Nat.mul 2 i) (commsK (nthP PS i))]) 6)

@[expose] noncomputable def g24F3K (LR : List (List (List Nat))) (Lb Lib : List Nat)
    (RS : List (List Nat)) (PS : List (List (List Nat × List Nat))) : Bool :=
  andB (andB (Nat.beq (lenN Lb) 6) (Nat.beq (lenN Lib) 6)) <|
  andB (allN 6 fun i => andB (andB (asciiK (nthLL LR i)) (shape12 (nthLL LR i)))
    (Nat.beq (packRows3 (res3Of (nthLL LR i)) 0 0) (nthV Lb i))) <|
  andB (allN 6 fun i => Nat.beq (mulF3 (nthV Lb i) (mulF3 (nthV Lb i) (nthV Lb i))) (nthV Lib i)) <|
  andB (allN 6 fun i => andB (Nat.beq (mulF3 (nthV Lb i) (nthV Lib i)) one3)
    (Nat.beq (mulF3 (nthV Lib i) (nthV Lb i)) one3)) <|
  andB (allLL (coverK RS PS) fun w => Nat.beq (word3 Lb Lib w) one3) <|
    letB (word3 Lb Lib [7, 7]) fun Z => andB (notB (Nat.beq Z one3)) (Nat.beq (mulF3 Z Z) one3)

end CFSG.KC.Misc.G24

end
