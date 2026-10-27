module

public import Certificates.Data.Kernel.Co1F2

public section

namespace CFSG.KC.U20

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

@[expose] noncomputable def wordK (G w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (idF (nat_lit 20)) (fun k _ ih => mulF (nat_lit 20) (getL (nat_lit 0) G k) ih) w

@[expose] noncomputable def lettersK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun k _ ih => andB (Nat.blt k (nat_lit 17)) ih) w

@[expose] noncomputable def gensK (G : List Nat) (L : List (Array Nat)) : Bool :=
  List.rec (motive := fun _ => List (Array Nat) → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun g _ ih L => List.rec (motive := fun _ => Bool) false
      (fun r t _ => andB (packB (nat_lit 20) r.toList g) (ih t)) L) G L

@[expose] noncomputable def flatK (F : List Nat) (L : List (Array Nat)) : Bool :=
  List.rec (motive := fun _ => List (Array Nat) → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun f _ ih L => List.rec (motive := fun _ => Bool) false
      (fun r t _ => andB (andB (Nat.blt f (pw2 (nat_lit 400))) (packB (nat_lit 20) r.toList f)) (ih t))
      L) F L

@[expose] noncomputable def wordsK (G F : List Nat) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun F => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) F)
    (fun w _ ih F => List.rec (motive := fun _ => Bool) false
      (fun f t _ => andB (andB (lettersK w) (Nat.beq (wordK G w) f)) (ih t)) F) W F

@[expose] noncomputable def selFrom (s : Nat) (F : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun f _ ih i => Nat.xor (nIf(bit s i, f, nat_lit 0)) (ih (Nat.succ i))) F

@[expose] noncomputable def selK (F : List Nat) (s : Nat) : Nat := selFrom s F (nat_lit 0)

@[expose] noncomputable def invFrom (F : List Nat) (D : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 400))
    (fun d _ ih i => andB (Nat.beq (selK F d) (pw2 i)) (ih (Nat.succ i))) D

@[expose] noncomputable def invK (F D : List Nat) : Bool := invFrom F D (nat_lit 0)

end CFSG.KC.U20

end
