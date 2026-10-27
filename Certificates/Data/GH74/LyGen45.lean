module

public import Certificates.Data.GH74.LyGen
public import Certificates.Data.CFSGNative.He.Fp

public section

namespace CFSG.Sporadic.Ly.Gen45

open CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.Ly.Gen

@[expose] def letterM (A B Bi : Array (Array Nat)) (z : Int) : Array (Array Nat) :=
  if z = 1 ∨ z = -1 then A else if z = 2 then B else Bi

@[expose] def wordM (A B Bi : Array (Array Nat)) (w : List Int) : Array (Array Nat) :=
  w.foldr (fun z P => mulM 5 111 (letterM A B Bi z) P) (idM 111)

@[expose] def bCheck (A B : Array (Array Nat)) : Bool :=
  let T := wordM A B (powM 5 111 B 4) genWords[5]!
  let D := powM 5 111 (mulM 5 111 A T) 3
  genWords[5]!.all (fun z => decide (z.natAbs ≤ 2)) &&
    mulM 5 111 D D == idM 111 &&
    D[0]![2]! % 5 != 0 &&
    D[0]![0]! % 5 != A[0]![0]! % 5 &&
    mulM 5 111 A D == mulM 5 111 D A &&
    mulM 5 111 T D == mulM 5 111 D T

@[expose] def bCertificate (_ : Unit) : Bool := bCheck matA matB

end CFSG.Sporadic.Ly.Gen45
