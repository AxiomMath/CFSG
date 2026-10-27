module

public import Certificates.Data.Kernel.Spor.Fi24R2W

public section

namespace CFSG.KC.Fi24F4J

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24R2W

@[expose] noncomputable def cwL (A B : List Nat) (z : Int) : List Nat :=
  Int.rec (motive := fun _ => List Nat)
    (fun m => Nat.rec (motive := fun _ => List Nat) B (fun k _ => Nat.rec (motive := fun _ => List Nat)
      A (fun _ _ => B) k) m)
    (fun m => Nat.rec (motive := fun _ => List Nat) (CFSG.KC.Fi24R2W.invC A)
      (fun _ _ => CFSG.KC.Fi24R2W.invC B) m) z

@[expose] noncomputable def cw (A B : List Nat) (w : List Int) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun z _ ih => cwL A B z ++ ih) w

@[expose] noncomputable def cwQ (A B : List Nat) (w : List Int) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun z _ ih => Int.rec (motive := fun _ => List Nat)
      (fun m => Nat.rec (motive := fun _ => List Nat) B (fun k _ => Nat.rec
        (motive := fun _ => List Nat) A (fun _ _ => B) k) m) (fun _ => B) z ++ ih) w

@[expose] noncomputable def repL (w : List Nat) (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun _ ih => w ++ ih) n

@[expose] noncomputable def nthW (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def nthV (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def prodW (X : List (List Nat)) (e : List Nat) : List Nat :=
  repL (nthW X 0) (nthV e 0) ++ (repL (nthW X 1) (nthV e 1) ++ (repL (nthW X 2) (nthV e 2) ++
    (repL (nthW X 3) (nthV e 3) ++ repL (nthW X 4) (nthV e 4))))

@[expose] noncomputable def digits3 (n : Nat) : List Nat :=
  [Nat.mod (Nat.div n 81) 3, Nat.mod (Nat.div n 27) 3, Nat.mod (Nat.div n 9) 3,
    Nat.mod (Nat.div n 3) 3, Nat.mod n 3]

@[expose] noncomputable def moves (NW : Nat → Nat → Nat) (w : List Nat) (b : Nat) : Bool :=
  Bool.not (Nat.beq (walkN NW w.reverse b) b)

@[expose] noncomputable def differ (NW : Nat → Nat → Nat) (u v : List Nat) (b : Nat) : Bool :=
  Bool.not (Nat.beq (walkN NW u.reverse b) (walkN NW v.reverse b))

end CFSG.KC.Fi24F4J

end
