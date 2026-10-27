module

public import CFSG.Quasithin.Vol2.KGFactE64L52Inputs

public section

namespace CFSG.KD.L52

open CFSG.Quasithin.H13.KGE64

@[expose] def pkR (f : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun p acc => Nat.lor acc (bif f p then Nat.shiftLeft 1 p else 0)) n

@[expose] def pkF (f : Nat → Bool) : Nat := pkR f 25

@[expose] def rowN (B k : Nat) : Nat := Nat.land (Nat.shiftRight B (Nat.mul 5 k)) 31

@[expose] def selN (A i k B : Nat) : Nat :=
  bif Nat.testBit A (Nat.add (Nat.mul 5 i) k) then rowN B k else 0

@[expose] def prodRowN (A B i : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (selN A i 0 B) (selN A i 1 B)) (selN A i 2 B)) (selN A i 3 B))
    (selN A i 4 B)

@[expose] def mMulN (A B : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.lor (prodRowN A B 0) (Nat.shiftLeft (prodRowN A B 1) 5))
    (Nat.shiftLeft (prodRowN A B 2) 10)) (Nat.shiftLeft (prodRowN A B 3) 15))
    (Nat.shiftLeft (prodRowN A B 4) 20)

@[expose] def mIdN : Nat := pkF fun p => p / 5 == p % 5

@[expose] def mPowN (A : Nat) : Nat → Nat
  | 0 => mIdN
  | k + 1 => mMulN A (mPowN A k)

@[expose] def mEqN (A B : Nat) : Bool :=
  (List.range 5).all fun i => (List.range 5).all fun j =>
    Nat.testBit A (5 * i + j) == Nat.testBit B (5 * i + j)

@[expose] def isUTN (A : Nat) : Bool :=
  (List.range 5).all fun i => (List.range 5).all fun j =>
    if j < i then !Nat.testBit A (5 * i + j) else if j = i then Nat.testBit A (5 * i + j)
    else true

@[expose] def ofCodeN (l : List Bool) : Nat :=
  pkF fun p =>
    if p / 5 = p % 5 then true
    else if p / 5 < p % 5 then l.getD (codeIdx (p / 5) (p % 5)) false
    else false

@[expose] def cj5N (pw : List Nat) (a : Nat) (i : Nat) : Nat :=
  mMulN (mMulN (pw.getD i 0) a) (pw.getD (7 - i) 0)

@[expose] def condA5N (pw : List Nat) (a : Nat) : Bool :=
  !mEqN a mIdN && mEqN (mMulN a a) mIdN && mEqN (mMulN (mMulN (cj5N pw a 3) (cj5N pw a 1)) a) mIdN

@[expose] def condB5N (pw : List Nat) (b : Nat) : Bool :=
  !mEqN b mIdN && mEqN (mMulN b b) mIdN && mEqN (mMulN (mMulN (cj5N pw b 3) (cj5N pw b 2)) b) mIdN

@[expose] def commAll5N (pw : List Nat) (a b : Nat) : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j =>
    mEqN (mMulN (cj5N pw a i) (cj5N pw b j)) (mMulN (cj5N pw b j) (cj5N pw a i))

@[expose] def l52StepN (Y k : Nat) : Bool :=
  let pw := (List.range 8).map (mPowN (mPowN Y k))
  let cand := ((bools 10).map ofCodeN).filter fun u =>
    (List.range' 1 6).all fun i => isUTN (cj5N pw u i)
  let A := cand.filter (condA5N pw)
  let B := cand.filter (condB5N pw)
  A.all fun a => B.all fun b => !commAll5N pw a b

@[expose] def l52CheckYN (Y : Nat) : Bool := (List.range' 1 6).all fun k => l52StepN Y k

@[expose] def l52YN (j : Nat) : Nat :=
  pkF fun p =>
    let r := p / 5
    let c := p % 5
    if c = j - 1 then r = j
    else if c = j then r = j + 1
    else if c = j + 1 then r = j - 1 || r = j
    else r = c

@[expose] def l52CheckN : Bool :=
  [1, 2, 3].all fun j => mEqN (mPowN (l52YN j) 7) mIdN && l52CheckYN (l52YN j)

end CFSG.KD.L52

end
