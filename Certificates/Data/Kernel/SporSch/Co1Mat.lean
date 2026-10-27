module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def rowK (X i : Nat) : Nat :=
  fld(X, Nat.mul (nat_lit 24) i, nat_lit 16777215)

@[expose] noncomputable def vmulK (v Y : Nat) : Nat :=
  foldN (nat_lit 24) (fun j s => nIf(hasBit v j, Nat.xor s (rowK Y j), s)) (nat_lit 0)

@[expose] noncomputable def mulK (X Y : Nat) : Nat :=
  foldN (nat_lit 24) (fun i s => Nat.lor s
    (Nat.shiftLeft (vmulK (rowK X i) Y) (Nat.mul (nat_lit 24) i))) (nat_lit 0)

@[expose] noncomputable def idM : Nat :=
  foldN (nat_lit 24) (fun i s => Nat.lor s
    (Nat.shiftLeft (Nat.shiftLeft (nat_lit 1) i) (Nat.mul (nat_lit 24) i))) (nat_lit 0)

@[expose] noncomputable def posK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun j _ ih => bAnd(bIf(Nat.beq j (nat_lit 1), true, Nat.beq j (nat_lit 2)), ih)) w

@[expose] noncomputable def wordPK (A B : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j _ ih acc => strictN (mulK acc (nIf(Nat.beq j (nat_lit 1), A, B))) ih) w idM

@[expose] noncomputable def wordEqK (A B : Nat) (w : List Nat) (R : Nat) : Bool :=
  bAnd(posK w, Nat.beq (wordPK A B w) R)

@[expose] noncomputable def parK (x : Nat) : Nat :=
  strictN (Nat.xor x (Nat.shiftRight x (nat_lit 16))) (fun a =>
  strictN (Nat.xor a (Nat.shiftRight a (nat_lit 8))) (fun b =>
  strictN (Nat.xor b (Nat.shiftRight b (nat_lit 4))) (fun c =>
  strictN (Nat.xor c (Nat.shiftRight c (nat_lit 2))) (fun d =>
    Nat.land (Nat.xor d (Nat.shiftRight d (nat_lit 1))) (nat_lit 1)))))

@[expose] noncomputable def actK (X v : Nat) : Nat :=
  foldN (nat_lit 24) (fun i s => nIf(Nat.beq (parK (Nat.land (rowK X i) v)) (nat_lit 1),
    Nat.lor s (Nat.shiftLeft (nat_lit 1) i), s)) (nat_lit 0)

@[expose] noncomputable def mulEqK (X Y Z : Nat) : Bool := Nat.beq (mulK X Y) Z

@[expose] noncomputable def invOKK (X Y : Nat) : Bool := Nat.beq (mulK X Y) idM

@[expose] noncomputable def letterK (M MI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), M (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    MI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def lettersK (k : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => bAnd(Nat.ble (nat_lit 2) c, bAnd(Nat.blt (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)) k,
      ih))) w

@[expose] noncomputable def wordSK (M MI : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun c _ ih acc => strictN (mulK acc (letterK M MI c)) ih) w idM

@[expose] noncomputable def lenLL (ws : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) ws

@[expose] noncomputable def dagK (M MI : Nat → Nat) (nb N : Nat) (ws : List (List Nat)) : Bool :=
  bAnd(Nat.beq (Nat.add nb (lenLL ws)) N,
  bAnd(allN N (fun k => invOKK (M k) (MI k)),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun w _ ih k => bAnd(lettersK k w, bAnd(Nat.beq (wordSK M MI w) (M k), ih (Nat.succ k))))
      ws nb))

end CFSG.KS.SporSch.M24

end
