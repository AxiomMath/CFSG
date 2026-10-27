module

public import Certificates.Data.CFSGNative.Perm.Chain
public import Certificates.Data.CFSGNative.Fi23.Slp

public section

namespace CFSG.Sporadic.Mathieu.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

structure Data where
  tA : Table
  tB : Table
  words : Array (List Int)
  base : Array Nat
  sizes : List Nat
  k : Nat
  pX : Nat
  eX : Nat
  pY : Nat
  eY : Nat
  pXY : Nat
  eXY : Nat

@[expose] def genAB (n : Nat) (D : Data) (z : Int) : Table :=
  if z = 1 then D.tA else if z = -1 then invT n D.tA else if z = 2 then D.tB else invT n D.tB

@[expose] def letters (n : Nat) (D : Data) : Array Table :=
  CFSG.Sporadic.Fi23.Native.slpLetters n (genAB n D) D.words

@[expose] def trees (n : Nat) (D : Data) : Array Tree := chainTrees n (letters n D) D.base

@[expose] def isIdT (n : Nat) (T : Table) : Bool := allIn 0 n fun i => ap T i == i

@[inline, expose] def inTreeB (T : Tree) (p : Nat) : Bool :=
  ap T.pos p < T.pts.size && ap T.pts (ap T.pos p) == p

@[expose] def orderOK (n : Nat) (T : Table) (p e : Nat) : Bool :=
  isIdT n (powT n (p ^ (e + 1)) T) && !isIdT n (powT n (p ^ e) T)

@[expose] def levelCover (n : Nat) (T : Array Tree) (i : Nat) : Bool :=
  allIn 0 n fun p => p < i || inTreeB T[i]! p

@[expose] def check (n : Nat) (D : Data) : Bool :=
  let L := letters n D
  let T := trees n D
  let Q := Array.range n
  invOK n D.tA (invT n D.tA) && invOK n D.tB (invT n D.tB) &&
    CFSG.Sporadic.Fi23.Native.slpOK D.words && CFSG.Sporadic.Fi23.Native.slpPure D.words &&
    2 ≤ D.words.size &&
    chainOK n L D.base Q D.base T 0 && orbitSizes T == D.sizes &&
    sift T L D.base Q 0 (apT D.tA Q) && sift T L D.base Q 0 (apT D.tB Q) &&
    D.k ≤ D.base.size && allIn 0 D.k (fun i => D.base[i]! == i && levelCover n T i) &&
    orderOK n L[0]! D.pX D.eX && orderOK n L[2]! D.pY D.eY &&
    orderOK n (compT n L[0]! L[2]!) D.pXY D.eXY

end CFSG.Sporadic.Mathieu.Native
