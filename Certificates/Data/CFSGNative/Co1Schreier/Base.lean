module

public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.Sporadic.Co1Schreier.Native

open CFSG.Sporadic.SmallF2.Native

abbrev Rows := Array Nat

@[expose] def mul (X Y : Rows) : Rows := mulRows 24 X Y

@[expose] def one (_ : Unit := ()) : Rows := idRows 24

@[expose] def inv (X : Rows) : Rows := Id.run do
  let mut M : Array Nat := Array.ofFn (n := 24) fun i =>
    ((X[i.val]?.getD 0) % 2 ^ 24) ||| (1 <<< (24 + i.val))
  for c in [0:24] do
    let mut p := 24
    for r in [c:24] do
      if p == 24 && (M[r]!).testBit c then p := r
    if p < 24 then
      let rp := M[p]!
      M := (M.set! p M[c]!).set! c rp
      for r in [0:24] do
        if r != c && (M[r]!).testBit c then M := M.set! r (M[r]! ^^^ rp)
  return M.map (· >>> 24)

@[expose] def add (X Y : Rows) : Rows :=
  Array.ofFn (n := 24) fun i => X[i.val]?.getD 0 ^^^ Y[i.val]?.getD 0

@[expose] def pow (X : Rows) : Nat → Rows
  | 0 => one
  | e + 1 => mul (pow X e) X

@[expose] def act (X : Rows) (v : Nat) : Nat := vecMulN 24 (transposeRows 24 X) v

@[expose] def letter (rs is : List Rows) (j : Int) : Rows :=
  if 0 < j then rs.getD (j.toNat - 1) one else is.getD ((-j).toNat - 1) one

@[expose] def word (rs is : List Rows) (w : List Int) : Rows :=
  w.foldl (fun acc j => mul acc (letter rs is j)) one

@[expose] def step (st : List Rows × List Rows × Bool) (w : List Int) :
    List Rows × List Rows × Bool :=
  let m := word st.1 st.2.1 w
  let mi := inv m
  (st.1 ++ [m], st.2.1 ++ [mi], st.2.2 && mul m mi == one)

@[expose] def dag (base : List Rows) (derivs : List (List Int)) : List Rows × List Rows × Bool :=
  derivs.foldl step (base, base.map inv, base.all fun b => mul b (inv b) == one)

@[expose] def decLetter (n : Nat) : Int :=
  if n % 2 = 0 then ((n / 2 : Nat) : Int) else -((n / 2 : Nat) : Int)

@[expose] def decWord (w : List Nat) : List Int := w.map decLetter

@[expose] def wf (X : Rows) : Bool := X.size == 24 && X.all (· < 2 ^ 24)

end CFSG.Sporadic.Co1Schreier.Native
