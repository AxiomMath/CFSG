module

public import CFSG.Certificates.Kernel.Orders.Mat3
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.KC.WordsS

open CFSG.KC.Ord

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def plane3 (r : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.add (cond (Nat.beq (x % 3) r) 1 0) (Nat.shiftLeft (plane3 r xs) 1)

@[expose] noncomputable def pk3 (N : Nat) (A : List Nat) : Nat :=
  Nat.add (plane3 1 A) (Nat.shiftLeft (plane3 2 A) N)

@[expose] noncomputable def step3 (d N LO CI RM A A2 : Nat) (Xs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun X _ ih => strictL X fun x => strictL (mul3s d N LO CI RM A x) fun y =>
      strictL (mul3s d N LO CI RM A2 x) fun z => x :: y :: z :: ih) Xs

@[expose] noncomputable def wordsS (d N LO CI RM ONE : Nat) (As : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [ONE]
    (fun A _ ih => strictL A fun a => strictL (mul3s d N LO CI RM a a) fun a2 =>
      step3 d N LO CI RM a a2 ih) As

@[expose] noncomputable def keyS (N : Nat) (pos : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ ih => Nat.add (Nat.land (Nat.shiftRight X i) 1)
    (Nat.add (Nat.mul 2 (Nat.land (Nat.shiftRight X (Nat.add N i)) 1)) (Nat.mul 3 ih))) pos

@[expose] noncomputable def wNodupS (d f N LO RM CI ONE UP : Nat) (key : Nat → Nat)
    (As : List (List Nat)) : Bool :=
  consts3OK d f N LO RM CI ONE UP && As.all (fun A => Nat.ble A.length N) &&
    CFSG.Decide.bitsetNodup ((wordsS d N LO CI RM ONE (As.map (pk3 N))).map key)

end CFSG.KC.WordsS

end
