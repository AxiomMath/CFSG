module

public import CFSG.Sporadic.Co2Jc.Words
public import CFSG.Sporadic.Co2Jc.Bits
public import CFSG.Sporadic.Co2Jc.Data.Derived

public section

namespace CFSG.Sporadic.Co2Jc.Native

open CFSG.Sporadic.Co2Jc.Data

@[expose] def sameOnBasis (w w' : List Nat) : Bool :=
  (List.range 10).all fun i => wordAct w (2 ^ i) == wordAct w' (2 ^ i)

@[expose] def wordOK (w w' : List Nat) : Bool :=
  sameOnBasis w w' && w.all (· < 3) && w'.all (· < 3)

@[expose] def gwList : List (List Nat) := [g1w, g2w]

@[expose] def invW : List (List Nat) :=
  [List.replicate 11 0, List.replicate 2 1, List.replicate 1 2]

@[expose] def orderOK (_ : Unit := ()) : Bool :=
  sameOnBasis (List.replicate 12 0) [] && sameOnBasis (List.replicate 3 1) [] &&
    sameOnBasis (List.replicate 2 2) []

@[expose] def conjOK (_ : Unit := ()) : Bool :=
  (List.range 3).all fun k =>
    (List.range 2).all fun i =>
      wordOK ([k] ++ gwList[i]! ++ invW[k]!) (dWord ((conjD[k]!)[i]!))

@[expose] def elemOK (_ : Unit := ()) : Bool :=
  wordOK [1] (dWord bD) && wordOK ([2] ++ List.replicate 11 0) (dWord caD) &&
    wordOK [0, 0] (dWord a2D)

@[expose] def phi (f m : Nat) : ZMod 2 :=
  bsum 10 m fun i => if f.testBit i then 1 else 0

@[expose] def pullList : List (List Nat) := [pullA, pullB, pullC]

@[expose] def pullK (k i : Nat) : Bool :=
  (pullList[k]!)[i]! < 22 &&
    (List.range 10).all fun j =>
      decide (Co2Smith.Native.glNJT k (2 ^ j) < 1024) &&
        phi (d22[(pullList[k]!)[i]!]!) (2 ^ j) ==
          phi (d22[i]!) (Co2Smith.Native.glNJT k (2 ^ j))

@[expose] def pullOK (_ : Unit := ()) : Bool :=
  pullList.length == 3 && d22.all (· < 1024) &&
    (List.range 3).all fun k => (List.range 22).all fun i => pullK k i

@[expose] def maskOK (_ : Unit := ()) : Bool :=
  d22.length == 22 && d22.all (· < 1024) &&
    ((List.range 22).all fun i =>
      (List.range 22).all fun j => i == j || d22[i]! != d22[j]!)

@[expose] def prodSwaps (l : List (List Nat)) (x : Nat) : Nat :=
  l.foldr (fun p acc => if acc = p[0]! then p[1]! else if acc = p[1]! then p[0]! else acc) x

@[expose] def signOK (_ : Unit := ()) : Bool :=
  swapsA.length == 19 &&
    swapsA.all (fun p => p.length == 2 && p.all (· < 22) && p[0]! != p[1]!) &&
    (List.range 22).all fun i => prodSwaps swapsA i == pullA[i]!

@[expose] def derivedOK (_ : Unit := ()) : Bool :=
  orderOK && conjOK && elemOK && pullOK && signOK && maskOK

end CFSG.Sporadic.Co2Jc.Native
