module

public import Certificates.Data.Kernel.GMS78RuS
public import Certificates.Data.Kernel.GMS78RuCzJ

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def pCodeOf (i : Nat) : Nat :=
  Nat.lor (Nat.shiftRight i 6) (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight i 3) 7) 8)
    (Nat.shiftLeft (Nat.land i 7) 11))

@[expose] noncomputable def pIdxOf (x : Nat) : Nat :=
  Nat.add (Nat.mul 64 (Nat.land x 255)) (Nat.add (Nat.mul 8 (Nat.land (Nat.shiftRight x 8) 7))
    (Nat.land (Nat.shiftRight x 11) 7))

@[expose] noncomputable def pMap (f : Nat → Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => List.cons (f x) ih) L

@[expose] noncomputable def pFilt (f : Nat → Bool) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x _ ih => Bool.rec (motive := fun _ => List Nat) ih (List.cons x ih) (f x)) L

@[expose] noncomputable def pAll : List Nat := pMap pCodeOf (sFilter 16384 fun _ => true)

@[expose] noncomputable def pInJ (m : Nat → Nat → Nat) (XS : List Nat) (p : Nat) : Bool :=
  neAllL (fun x => (fun px xp => orB (Nat.beq px xp) (Nat.beq px (m 256 xp))) (m p x) (m x p)) XS

@[expose] noncomputable def pInCX (m : Nat → Nat → Nat) (XS : List Nat) (p : Nat) : Bool :=
  neAllL (fun x => Nat.beq (m p x) (m x p)) XS

@[expose] noncomputable def pBit (S i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight S i) 1) 1

@[expose] noncomputable def pJMem (JM x : Nat) : Bool := pBit JM (pIdxOf x)

@[expose] noncomputable def pJL (JM : Nat) : List Nat :=
  pMap pCodeOf (sFilter 16384 (pBit JM))

@[expose] noncomputable def pCmt (m : Nat → Nat → Nat) (q p : Nat) : Bool := Nat.beq (m p q) (m q p)

@[expose] noncomputable def pEvenD (x : Nat) : Bool := pBit 51 (Nat.shiftRight x 11)

@[expose] noncomputable def pCount (f : Nat → Bool) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun p _ ih => strictN ih fun a => Bool.rec (motive := fun _ => Nat) a (Nat.succ a) (f p)) L

@[expose] noncomputable def kA117 (m : Nat → Nat → Nat) (XS : List Nat) (JM : Nat) : Bool :=
  andB (pInJ m XS 102) <| andB (notB (pInCX m XS 102)) <| andB (Nat.beq (m 102 102) 0) <|
  andB (Nat.beq (pCount (pCmt m 102) pAll) 1024) <|
  andB (pInJ m XS 9216) <| andB (notB (pInCX m XS 9216)) <|
  neAllL (fun d => czAny (fun x => Nat.beq (Nat.shiftRight x 11) d) (pJL JM)) [0, 1, 4, 5]

@[expose] noncomputable def kLists117 (m : Nat → Nat → Nat) (XS : List Nat) (JM : Nat)
    (CXL F1L KL : List Nat) : Bool :=
  andB (czListEq CXL (pFilt (fun x => andB (notB (pInCX m XS x)) (Nat.beq (m x x) 0)) (pJL JM))) <|
  andB (czListEq (pMap (fun e => Nat.land e 16383) F1L) (pFilt
    (fun y => andB (pCmt m 102 y) (andB (pJMem JM (m y y)) (andB (notB (pJMem JM y))
      (notB (pEvenD y))))) pAll)) <|
  czListEq (pMap (fun e => Nat.land e 16383) KL)
    (pFilt (fun k => andB (pInCX m XS k) (Nat.beq (m (m k 9216) (m k 9216)) 0)) (pJL JM))

@[expose] noncomputable def kF1 (m : Nat → Nat → Nat) (JM e : Nat) : Bool :=
  (fun y j => andB (Nat.blt j 16384) (andB (pJMem JM j) (andB (pCmt m 102 j)
    (Nat.beq (m (m y j) (m y j)) 0)))) (Nat.land e 16383) (Nat.shiftRight e 14)

@[expose] noncomputable def kF3 (m : Nat → Nat → Nat) (JM e : Nat) : Bool :=
  (fun k u => (fun c => andB (Nat.blt u 16384) (andB (pCmt m c u) (andB (pJMem JM (m u u))
      (andB (notB (pJMem JM u)) (andB (notB (pEvenD u))
        (neAllL (fun j => orB (notB (pCmt m c j)) (notB (Nat.beq (m (m u j) (m u j)) 0)))
          (pJL JM)))))))
    (m k 9216)) (Nat.land e 16383) (Nat.shiftRight e 14)

@[expose] noncomputable def kCx (m : Nat → Nat → Nat) (JM x : Nat) : Bool :=
  Nat.ble (pCount (pCmt m x) (pJL JM)) 128

@[expose] noncomputable def kJM (m : Nat → Nat → Nat) (XS : List Nat) (JM i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (notB (pInJ m XS (pCodeOf i))) (pInJ m XS (pCodeOf i))
    (pBit JM i)

end CFSG.KC.GMS

end
