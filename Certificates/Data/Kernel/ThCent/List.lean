module

public import Certificates.Data.Kernel.ThCent.Pin

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def wordRFrom (c rm : Nat) (V : Nat → Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun r _ ih acc => strictF (mulB c rm acc (V r)) ih) w

@[expose] noncomputable def wordR (c rm ONE : Nat) (V : Nat → Nat) (w : List Nat) : Nat :=
  wordRFrom c rm V w ONE

@[expose] noncomputable def neB (c rm ONE X Y : Nat) : Bool :=
  notB (Nat.beq (mulB c rm X ONE) (mulB c rm Y ONE))

@[expose] noncomputable def witR (c rm ONE : Nat) (V : Nat → Nat) (E : Nat) :
    List (List Nat × List Nat) → Nat → Option Nat :=
  List.rec (motive := fun _ => Nat → Option Nat) (fun acc => some acc)
    (fun p _ ih acc => strictF (wordR c rm ONE V p.1) fun W => strictF (wordR c rm ONE V p.2)
      fun Wi => Bool.rec (motive := fun _ => Option Nat) none
        (strictF (mulB c rm (mulB c rm (mulB c rm acc W) E) Wi) ih)
        (Nat.beq (mulB c rm W Wi) ONE))

@[expose] noncomputable def eltOK (c rm ONE : Nat) (V : Nat → Nat) (Z m : Nat) (w : List Nat)
    (ws : List (List Nat × List Nat)) (v : Nat) : Bool :=
  strictF (wordR c rm ONE V w) fun E =>
    andB (Nat.beq (mulB c rm E Z) (mulB c rm Z E))
      (andB (Nat.beq (rowB rm E 0) v)
        (Bool.or (Nat.beq E ONE)
          (Option.rec (motive := fun _ => Bool) false
            (fun P => notB (Nat.beq (powB c rm ONE P m (nat_lit 5)) ONE))
            (witR c rm ONE V E ws E))))

@[expose] noncomputable def eltRec (c rm ONE : Nat) (V : Nat → Nat) (Z m : Nat)
    (e : List Nat × List (List Nat × List Nat) × Nat) : Bool :=
  eltOK c rm ONE V Z m e.1 e.2.1 e.2.2

@[expose] def chunkOK {α : Type} (f : α → Bool) (E : List α) (lo n : Nat) : Bool :=
  ((E.drop lo).take n).all f

@[expose] noncomputable def distinctL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x t ih => andB (List.rec (motive := fun _ => Bool) true
      (fun y _ ih' => andB (notB (Nat.beq x y)) ih') t) ih) l

@[expose] noncomputable def pairOK7 (c rm ONE X Y : Nat) : Bool :=
  andB (Nat.beq (powB c rm ONE X 7 (nat_lit 3)) ONE)
    (andB (Nat.beq (powB c rm ONE Y 7 (nat_lit 3)) ONE)
      (andB (Nat.beq (mulB c rm X Y) (mulB c rm Y X))
        (andB (neB c rm ONE X ONE)
          ((List.range 7).all fun k => neB c rm ONE Y (powB c rm ONE X k (nat_lit 3))))))

@[expose] noncomputable def conjOK7 (c rm ONE : Nat) (V : Nat → Nat) (X Y Z a b : Nat)
    (u : List Nat) : Bool :=
  strictF (wordR c rm ONE V u) fun M =>
    Nat.beq (mulB c rm M (mulB c rm (powB c rm ONE X a (nat_lit 3))
      (powB c rm ONE Y b (nat_lit 3)))) (mulB c rm Z M)

@[expose] noncomputable def cubeP (c rm ONE X Y C i j k : Nat) : Nat :=
  mulB c rm (mulB c rm (powB c rm ONE X i (nat_lit 3)) (powB c rm ONE Y j (nat_lit 3)))
    (powB c rm ONE C k (nat_lit 3))

@[expose] noncomputable def cubeOK5 (c rm ONE X Y C : Nat) : Bool :=
  andB (Nat.beq (powB c rm ONE X 5 (nat_lit 3)) ONE)
    (andB (Nat.beq (powB c rm ONE Y 5 (nat_lit 3)) ONE)
      (andB (Nat.beq (mulB c rm C X) (mulB c rm X C))
        (Nat.beq (mulB c rm C Y) (mulB c rm Y C))))

@[expose] noncomputable def cubeRowOK (c rm ONE X Y C i j k v : Nat) : Bool :=
  Nat.beq (rowB rm (cubeP c rm ONE X Y C i j k) 0) v

@[expose] noncomputable def conjOK5 (c rm ONE : Nat) (V : Nat → Nat) (X Y C i j k : Nat)
    (u : List Nat) : Bool :=
  strictF (wordR c rm ONE V u) fun M =>
    Nat.beq (mulB c rm M (cubeP c rm ONE X Y C i j k)) (mulB c rm C M)

end CFSG.KC.ThCent

end
