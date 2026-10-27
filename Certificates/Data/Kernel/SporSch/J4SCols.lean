module

public import Certificates.Data.Kernel.SporSch.J4STok
public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.KS.Mathieu

@[expose] noncomputable def ent (w P i : Nat) : Nat :=
  fld(P, Nat.mul w i, Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def colK (P j : Nat) : Nat :=
  fld(P, Nat.mul (nat_lit 11) j, nat_lit 2047)

@[expose] noncomputable def appK (P a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1))
      (nat_lit 1), Nat.xor s (colK P j), s))) (nat_lit 11)

@[expose] noncomputable def packK (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc (fun s => Nat.lor s (Nat.shiftLeft (f j) (Nat.mul (nat_lit 11) j))))
    (nat_lit 11)

@[expose] noncomputable def compK (P Q : Nat) : Nat := packK (fun j => appK P (colK Q j))

@[expose] noncomputable def pidK : Nat := packK (fun j => Nat.shiftLeft (nat_lit 1) j)

@[expose] noncomputable def canonK (P : Nat) : Bool :=
  Nat.beq (Nat.shiftRight P (nat_lit 121)) (nat_lit 0)

@[expose] noncomputable def bindWK (w m : Nat) (l : List Nat) (P : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun j acc => bAnd(Nat.beq j m, Nat.beq acc P))
    (fun x _ ih j acc => bAnd(Nat.blt x (Nat.shiftLeft (nat_lit 1) w),
      strictB (Nat.lor acc (Nat.shiftLeft x (Nat.mul w j))) (fun acc' =>
        ih (Nat.succ j) acc')))
    l (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def bind2K (w m : Nat) (L : List (Array Nat)) (T : Nat → Nat) (n : Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k n)
    (fun a _ ih k => bAnd(bindWK w m a.toList (T k), ih (Nat.succ k))) L (nat_lit 0)

@[expose] noncomputable def letK (X XI Y YI : Nat) (l : Int) (a : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 1), appK X a, nIf(Nat.beq k (nat_lit 2), appK Y a, a)))
    (fun k => nIf(Nat.beq k (nat_lit 0), appK XI a, nIf(Nat.beq k (nat_lit 1), appK YI a, a))) l

@[expose] noncomputable def wordAppK (X XI Y YI : Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun l _ ih a => strictN (ih a) (fun b => letK X XI Y YI l b)) w

@[expose] noncomputable def wordColsK (X XI Y YI : Nat) (w : List Int) : Nat :=
  packK (fun j => wordAppK X XI Y YI w (Nat.shiftLeft (nat_lit 1) j))

@[expose] noncomputable def fixCntK (P : Nat) : Nat :=
  foldN (nat_lit 2048) (fun a s => nIf(Nat.beq (appK P a) a, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def xorSubK (V : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun v _ ih m => Nat.xor (nIf(Nat.beq (Nat.mod m (nat_lit 2)) (nat_lit 1), v, nat_lit 0))
      (ih (Nat.div m (nat_lit 2)))) V

@[expose] noncomputable def spanK (V : List Nat) : Bool :=
  Nat.beq (foldN (nat_lit 2048) (fun m s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (xorSubK V m)))
    (nat_lit 0)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)) (nat_lit 1))

@[expose] noncomputable def intEqK (x y : Int) : Bool := Nat.beq (icode x) (icode y)

@[expose] noncomputable def seqK (w : List Int) : List Int → (List Int → Bool) → Bool :=
  List.rec (motive := fun _ => List Int → (List Int → Bool) → Bool) (fun L k => k L)
    (fun x _ ih L k => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => bAnd(intEqK x y, ih ys k)) L) w

@[expose] noncomputable def lenI (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) w

@[expose] noncomputable def tokWordsK (L : List Int) (ws : List (List Int)) : Bool :=
  List.rec (motive := fun _ => List Int → Bool) (fun _ => true)
    (fun w _ ih L => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => bAnd(intEqK y (Int.ofNat (lenI w)), seqK w ys ih)) L) ws L

end CFSG.KS.SporSch.C11

end
