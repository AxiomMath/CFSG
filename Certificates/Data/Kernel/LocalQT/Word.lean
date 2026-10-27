module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.LQT.W

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def wordC (n ca cb : Nat) (l : List Char) : Nat :=
  List.rec (motive := fun _ => Nat) (one n)
    (fun ch _ ih => mul n
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (inv n cb) cb (Nat.beq (Char.toNat ch) (nat_lit 98)))
        ca (Nat.beq (Char.toNat ch) (nat_lit 97)))
      ih) l

@[expose] noncomputable def distinct (m : Nat) (f : Nat → Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (Nat.rec (motive := fun _ => Bool) true
      (fun j ih2 => andB (notB (Nat.beq (f i) (f j))) ih2) i) ih) m

@[expose] noncomputable def sq3C (n X Y H a b c d : Nat) : Bool :=
  andB (Nat.beq (pow n X 3) (one n)) (andB (Nat.beq (pow n Y 3) (one n))
  (andB (comm n X Y)
  (andB (distinct 9 fun t => mul n (pow n X (Nat.mod t 3)) (pow n Y (Nat.div t 3)))
  (andB (Nat.beq (conj n H X) (mul n (pow n X a) (pow n Y b)))
    (Nat.beq (conj n H Y) (mul n (pow n X c) (pow n Y d)))))))

@[expose] noncomputable def sq3OK (n ca cb : Nat) (lx ly lh : List Char) (a b c d : Nat) : Bool :=
  letB (wordC n ca cb lx) fun X => letB (wordC n ca cb ly) fun Y =>
    letB (wordC n ca cb lh) fun H => sq3C n X Y H a b c d

@[expose] noncomputable def cub3C (n X Y H a b c d e f μ : Nat) : Bool :=
  letB (mul n (mul n (mul n X Y) (inv n X)) (inv n Y)) fun Z =>
  andB (Nat.beq (pow n X 3) (one n)) (andB (Nat.beq (pow n Y 3) (one n))
  (andB (notB (Nat.beq Z (one n))) (andB (comm n Z X) (andB (comm n Z Y)
  (andB (distinct 27 fun t =>
      mul n (mul n (pow n X (Nat.mod t 3)) (pow n Y (Nat.mod (Nat.div t 3) 3)))
        (pow n Z (Nat.div t 9)))
  (andB (Nat.beq (conj n H X) (mul n (mul n (pow n X a) (pow n Y b)) (pow n Z c)))
  (andB (Nat.beq (conj n H Y) (mul n (mul n (pow n X d) (pow n Y e)) (pow n Z f)))
    (Nat.beq (conj n H Z) (pow n Z μ)))))))))

@[expose] noncomputable def cub3OK (n ca cb : Nat) (lx ly lh : List Char)
    (a b c d e f μ : Nat) : Bool :=
  letB (wordC n ca cb lx) fun X => letB (wordC n ca cb ly) fun Y =>
    letB (wordC n ca cb lh) fun H => cub3C n X Y H a b c d e f μ

@[expose] noncomputable def genAt (n : Nat) (G : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => one n)
    (fun x _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) G i

@[expose] noncomputable def evalWK (n : Nat) (G : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (one n) (fun i _ ih => mul n (genAt n G i) ih) w

@[expose] noncomputable def wordsOK (n : Nat) (G B : List (Nat)) (W : List (List Nat)) : Bool :=
  andB (Nat.ble n 32) (List.rec (motive := fun _ => List Nat → Bool)
    (fun B => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) B)
    (fun w _ ih B => List.rec (motive := fun _ => Bool) false
      (fun b bs _ => andB (Nat.beq b (evalWK n G w)) (ih bs)) B) W B)

end CFSG.KC.LQT.W

end
