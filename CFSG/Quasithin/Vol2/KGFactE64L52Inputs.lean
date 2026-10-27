module

public import Init

public section

namespace CFSG.Quasithin.H13.KGE64

@[expose] def m5 (A : List Bool) (i j : Nat) : Bool := A.getD (5 * i + j) false

@[expose] def mMul (A B : List Bool) : List Bool :=
  (List.range 25).map fun p =>
    (m5 A (p / 5) 0 && m5 B 0 (p % 5)) ^^ (m5 A (p / 5) 1 && m5 B 1 (p % 5)) ^^
      (m5 A (p / 5) 2 && m5 B 2 (p % 5)) ^^ (m5 A (p / 5) 3 && m5 B 3 (p % 5)) ^^
      (m5 A (p / 5) 4 && m5 B 4 (p % 5))

@[expose] def mId : List Bool := (List.range 25).map fun p => p / 5 == p % 5

@[expose] def mPow (A : List Bool) : Nat → List Bool
  | 0 => mId
  | k + 1 => mMul A (mPow A k)

@[expose] def mEq (A B : List Bool) : Bool :=
  (List.range 5).all fun i => (List.range 5).all fun j => m5 A i j == m5 B i j

@[expose] def isUT (A : List Bool) : Bool :=
  (List.range 5).all fun i => (List.range 5).all fun j =>
    if j < i then !m5 A i j else if j = i then m5 A i j else true

@[expose] def codeIdx (i j : Nat) : Nat := 4 * i - i * (i - 1) / 2 + j - i - 1

@[expose] def ofCode (l : List Bool) : List Bool :=
  (List.range 25).map fun p =>
    if p / 5 = p % 5 then true
    else if p / 5 < p % 5 then l.getD (codeIdx (p / 5) (p % 5)) false
    else false

@[expose] def bools : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bools n).flatMap fun l => [false :: l, true :: l]

@[expose] def cj5 (pw : List (List Bool)) (a : List Bool) (i : Nat) : List Bool :=
  mMul (mMul (pw.getD i []) a) (pw.getD (7 - i) [])

@[expose] def condA5 (pw : List (List Bool)) (a : List Bool) : Bool :=
  !mEq a mId && mEq (mMul a a) mId && mEq (mMul (mMul (cj5 pw a 3) (cj5 pw a 1)) a) mId

@[expose] def condB5 (pw : List (List Bool)) (b : List Bool) : Bool :=
  !mEq b mId && mEq (mMul b b) mId && mEq (mMul (mMul (cj5 pw b 3) (cj5 pw b 2)) b) mId

@[expose] def commAll5 (pw : List (List Bool)) (a b : List Bool) : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j =>
    mEq (mMul (cj5 pw a i) (cj5 pw b j)) (mMul (cj5 pw b j) (cj5 pw a i))

@[expose] def l52CheckY (y : List Bool) : Bool :=
  (List.range' 1 6).all fun k =>
    let pw := (List.range 8).map (mPow (mPow y k))
    let cand := ((bools 10).map ofCode).filter fun u =>
      (List.range' 1 6).all fun i => isUT (cj5 pw u i)
    let A := cand.filter (condA5 pw)
    let B := cand.filter (condB5 pw)
    A.all fun a => B.all fun b => !commAll5 pw a b

@[expose] def l52Y (j : Nat) : List Bool :=
  (List.range 25).map fun p =>
    let r := p / 5
    let c := p % 5
    if c = j - 1 then r = j
    else if c = j then r = j + 1
    else if c = j + 1 then r = j - 1 || r = j
    else r = c

@[expose] def l52Check : Bool :=
  [1, 2, 3].all fun j => mEq (mPow (l52Y j) 7) mId && l52CheckY (l52Y j)

end CFSG.Quasithin.H13.KGE64
