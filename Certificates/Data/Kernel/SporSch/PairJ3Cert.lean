module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.SporSch

@[expose] noncomputable def le70K (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ch _ ih => bAnd(Nat.ble (Char.toNat ch) (nat_lit 70), ih)) cs

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def natsI (l : List Nat) (tl : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) tl (fun x _ ih => Int.ofNat x :: ih) l

@[expose] noncomputable def orbsI (os : List (List Nat)) (tl : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) tl (fun o _ ih => Int.ofNat (lenK o) :: natsI o ih) os

@[expose] noncomputable def trisI (ts : List (Nat × Nat × Nat)) (tl : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) tl
    (fun t _ ih => Int.ofNat t.1 :: Int.ofNat t.2.1 :: Int.ofNat t.2.2 :: ih) ts

@[expose] noncomputable def msI (ms : List (Nat × List (Nat × Nat × Nat))) (tl : List Int) :
    List Int :=
  List.rec (motive := fun _ => List Int) tl
    (fun m _ ih => Int.ofNat m.1 :: Int.ofNat (lenK m.2) :: trisI m.2 ih) ms

@[expose] noncomputable def encOM (R : List (List Nat) × List (Nat × List (Nat × Nat × Nat))) :
    List Int :=
  Int.ofNat (lenK R.1) :: orbsI R.1 (Int.ofNat (lenK R.2) :: msI R.2 [])

@[expose] noncomputable def incK (n : Nat) (o : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih lo => bAnd(Nat.ble lo x, bAnd(Nat.blt x n, ih (Nat.succ x)))) o

@[expose] noncomputable def nilLK {α : Type} (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

@[expose] noncomputable def orbsK (n : Nat) (os : List (List Nat)) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun ls => nilLK ls)
    (fun o _ ih ls => List.rec (motive := fun _ => Bool) false
      (fun l ls' _ => bAnd(Nat.beq (lenK o) l, bAnd(incK n o (nat_lit 0), ih ls'))) ls) os

@[expose] noncomputable def trisK (n : Nat) (ts : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ ih => Prod.rec (motive := fun _ => Bool)
      (fun i uv => Prod.rec (motive := fun _ => Bool)
        (fun u v => bAnd(Nat.blt i (nat_lit 2), bAnd(Nat.blt u n, bAnd(Nat.blt v n, ih)))) uv) t)
    ts

@[expose] noncomputable def msK (n c : Nat) (ms : List (Nat × List (Nat × Nat × Nat))) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun rs => nilLK rs)
    (fun m _ ih rs => List.rec (motive := fun _ => Bool) false
      (fun r rs' _ => Prod.rec (motive := fun _ => Bool)
        (fun a ts => bAnd(Nat.beq a r, bAnd(Nat.beq (lenK ts) c, bAnd(trisK n ts, ih rs')))) m) rs)
    ms

@[expose] noncomputable def stabK (n c : Nat) (ls rs : List Nat)
    (R : List (List Nat) × List (Nat × List (Nat × Nat × Nat))) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun os ms => bAnd(orbsK n os ls, msK n c ms rs)) R

end CFSG.KS.SporSch

end
