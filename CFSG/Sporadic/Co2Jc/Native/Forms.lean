module

public import CFSG.Sporadic.Co2Jc.Bits
public import CFSG.Sporadic.Co2Jc.Data.Forms

public section

namespace CFSG.Sporadic.Co2Jc.Native

open CFSG.Sporadic.Co2Jc.Data

@[expose] def uBilin (p q : Nat) : Nat := 1 <<< (10 * p + q)

@[expose] def pairMask (x y : Nat) : Nat :=
  colAct (fun p => colAct (fun q => uBilin p q) y) x

@[expose] def bilinEq (k i j : Nat) : Nat :=
  pairMask (Co2Smith.Native.glNJT k (2 ^ i)) (Co2Smith.Native.glNJT k (2 ^ j)) ^^^ uBilin i j

@[expose] def bilinEqsList : List Nat :=
  [0, 2].flatMap fun k =>
    (List.range 10).flatMap fun i => (List.range 10).map fun j => bilinEq k i j

@[expose] def bilinEqs : Array Nat := bilinEqsList.toArray

@[expose] def uWedge (p q r : Nat) : Nat := 1 <<< (10 * (10 * p + q) + r)

@[expose] def wedLhs (k i j r : Nat) : Nat :=
  colAct (fun p => colAct (fun q => if p = q then 0 else uWedge (min p q) (max p q) r)
    (Co2Smith.Native.glNJT k (2 ^ j))) (Co2Smith.Native.glNJT k (2 ^ i))

@[expose] def wedRhs (k i j r : Nat) : Nat :=
  xorList ((List.range 10).map fun s =>
    if (Co2Smith.Native.glNJT k (2 ^ s)).testBit r then uWedge i j s else 0)

@[expose] def wedEq (k i j r : Nat) : Nat := wedLhs k i j r ^^^ wedRhs k i j r

@[expose] def wedEqsList : List Nat :=
  [0, 2].flatMap fun k =>
    (List.range 10).flatMap fun i =>
      (List.range 10).flatMap fun j =>
        if i < j then (List.range 10).map fun r => wedEq k i j r else []

@[expose] def wedEqs : Array Nat := wedEqsList.toArray

@[expose] def foldEqs (E : Array Nat) (m : Nat) : Nat :=
  ((List.range E.size).filter fun e => m.testBit e).foldl (fun acc e => acc ^^^ E[e]!) 0

@[expose] def bilinCheck : Bool :=
  bilinUnits.length == 100 &&
    (List.range 100).all fun u => foldEqs bilinEqs (bilinUnits[u]!) == 1 <<< u

@[expose] def wedgeCheck : Bool :=
  wedUnits.length == 1000 &&
    (List.range 10).all fun i => (List.range 10).all fun j =>
      if i < j then
        (List.range 10).all fun r =>
          foldEqs wedEqs (wedUnits[10 * (10 * i + j) + r]!) == 1 <<< (10 * (10 * i + j) + r)
      else true

@[expose] def formsOK : Bool := bilinCheck && wedgeCheck

end CFSG.Sporadic.Co2Jc.Native
