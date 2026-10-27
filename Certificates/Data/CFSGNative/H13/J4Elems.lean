module

public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.H13.J4.Native

open CFSG.Sporadic.J4.Native

@[expose] def uLetters (_ : Unit := ()) : List Int :=
  (List.replicate 9 [-2, -1]).flatten ++ (List.replicate 5 [1, 2, 1, 2, 2]).flatten ++
    (List.replicate 9 [1, 2]).flatten

@[expose] def vLetters (_ : Unit := ()) : List Int :=
  (List.replicate 16 [1, 2, 2, 2]).flatten ++ (List.replicate 8 [1, 2, 1, 2, 1, 2, 2]).flatten ++
    (List.replicate 21 [1, 2, 2, 2]).flatten

@[expose] def uvPairsOf (bp : Array Pr) : Array Pr := #[prWord bp uLetters, prWord bp vLetters]

@[expose] def dOf (uv : Array Pr) : Pr :=
  prMul (prMul (prMul (prInv (uv[1]?.getD prOne)) (uv[0]?.getD prOne)) (uv[1]?.getD prOne))
    (uv[0]?.getD prOne)

@[expose] def tOf (uv : Array Pr) : Pr := prPow (dOf uv) 22

@[expose] def rOf (uv : Array Pr) : Pr := prPow (dOf uv) 11

@[expose] def rConjOf (uv : Array Pr) (c : List Int) : Pr :=
  prMul (prMul (prWord uv c) (rOf uv)) (prInv (prWord uv c))

@[expose] def vNe (a b : V2) : Bool := (List.range 112).any fun j => a.testBit j != b.testBit j

@[expose] def rowsNe (X Y : Array V2) : Bool :=
  (List.range 112).any fun i => vNe (X[i]?.getD V2.zero) (Y[i]?.getD V2.zero)

@[expose] def addRows (X Y : Array V2) : Array V2 :=
  Array.ofFn (n := 112) fun i => (X[i.val]?.getD V2.zero).xor (Y[i.val]?.getD V2.zero)

@[expose] def rowsZero (X : Array V2) : Bool :=
  (List.range 112).all fun i => (List.range 112).all fun j => !((X[i]?.getD V2.zero).testBit j)

@[expose] def rowsAgree (X : Array V2) (d : Nat) (f : Nat → Nat → Bool) : Bool :=
  (List.range d).all fun i => (List.range d).all fun j => (X[i]?.getD V2.zero).testBit j == f i j

end CFSG.Quasithin.H13.J4.Native
