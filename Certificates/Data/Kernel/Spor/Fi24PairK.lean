module

public import CFSG.Certificates.Kernel.Common.Lce
public import Certificates.Data.Kernel.Spor.Fi24NetPt

public section

namespace CFSG.KC.Fi24PairK

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt

@[expose] noncomputable def invW (w : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) List.nil (fun z _ ih => ih ++ [Int.neg z]) w

@[expose] noncomputable def posZ (z : Int) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun _ => true) (fun _ => false) z

@[expose] noncomputable def dirZ (net : Nat → Bool) (z : Int) : Bool :=
  orB (Nat.ble z.natAbs (nat_lit 2)) (net (Nat.sub z.natAbs (nat_lit 3)))

@[expose] noncomputable def dirOK (net : Nat → Bool) (w : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih => andB (dirZ net z) ih) w

@[expose] noncomputable def flatF (W : Nat → List Int) (net : Nat → Bool) (d : Nat) : Int → List Int :=
  Nat.rec (motive := fun _ => Int → List Int) (fun z => [z])
    (fun _ ih z => Bool.rec (motive := fun _ => List Int)
      ((fun u => Bool.rec (motive := fun _ => List Int) (invW u) u (posZ z))
        (List.rec (motive := fun _ => List Int) List.nil (fun y _ r => ih y ++ r)
          (W (Nat.sub z.natAbs (nat_lit 3)))))
      [z] (dirZ net z)) d

@[expose] noncomputable def ptZ (NW : Nat → Nat → Nat) (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => nIf(Nat.beq m (nat_lit 0), ptR (NW (lidx m)) x, ptF (NW (lidx m)) x))
    (fun n => nIf(Nat.beq n (nat_lit 0), ptF (NW (nat_lit 0)) x, ptR (NW (lidx (Nat.succ n))) x)) z

@[expose] noncomputable def apZ (NW : Nat → Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (ih x) (fun y => ptZ NW z y)) w x

@[expose] noncomputable def fixW (NW : Nat → Nat → Nat) (w : List Int) (B : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => bAnd(Nat.beq (apZ NW w b) b, ih)) B

@[expose] noncomputable def stepW (NW : Nat → Nat → Nat) (ws : List (List Int)) (S : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) S (fun w _ ih => Nat.lor (walkW NW w S) ih) ws

@[expose] noncomputable def iterW (NW : Nat → Nat → Nat) (ws : List (List Int)) (d S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun _ ih => strictN ih (stepW NW ws)) d

@[expose] noncomputable def orbW (NW : Nat → Nat → Nat) (ws : List (List Int)) (d y c : Nat) : Bool :=
  letB (iterW NW ws d (Nat.shiftLeft (nat_lit 1) y)) (fun P =>
    andB (Nat.beq (stepW NW ws P) P) (Nat.beq (popcount P (nat_lit 524288)) c))

end CFSG.KC.Fi24PairK

end
