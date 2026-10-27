module

public import CFSG.Sporadic.Co2Jc.Words
public import CFSG.Sporadic.Co2Jc.Bits
public import CFSG.Sporadic.Co2Jc.Data.Rels
public import CFSG.Sporadic.Co2Jc.Data.CocycleDual
public import CFSG.Sporadic.Co2Jc.Data.CocycleSplit

public section

namespace CFSG.Sporadic.Co2Jc.Native

open CFSG.Sporadic.Co2Jc (wordAct xorList)
open CFSG.Sporadic.Co2Jc.Data

@[expose] def gl (k x : Nat) : Nat := CFSG.Sporadic.Co2Smith.Native.glNJT k x

@[expose] def ten : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

@[expose] def ofWords : List Nat → Nat
  | [] => 0
  | w :: l => w + ofWords l * 4294967296

@[expose] def rowOf : List Nat → Nat → Nat
  | [], _ => 0
  | k :: w, m => rowOf w m ^^^ (wordAct w m <<< (10 * k))

@[expose] def dualRows : List Nat :=
  rels.flatMap fun r => (List.range 10).map fun j => rowOf r (2 ^ j)

@[expose] def xorRowsFrom (i : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | r :: rs, m => (if m.testBit i then r else 0) ^^^ xorRowsFrom (i + 1) rs m

@[expose] def xorRowsByMask (rows : List Nat) (m : Nat) : Nat := xorRowsFrom 0 rows m

@[expose] def dualTarget (k b : Nat) : Nat :=
  xorList ((2 ^ (10 * k + b)) :: cocycleDualP[b]! ::
    ten.map fun bp => if (gl k (2 ^ b)).testBit bp then cocycleDualP[bp]! else 0)

@[expose] def relOK : Bool :=
  rels.all (fun r => r.all (· < 3) && (List.range 10).all fun j => wordAct r (2 ^ j) == 2 ^ j)

@[expose] def dualCombOK : Bool :=
  (List.range 30).all fun u =>
    xorRowsByMask dualRows (cocycleDualComb[u]!) == dualTarget (u / 10) (u % 10)

@[expose] def dualRowsLenOK : Bool := dualRows.length == 250

@[expose] def dualPLenOK : Bool := cocycleDualP.length == 10

@[expose] def dualCombLenOK : Bool := cocycleDualComb.length == 30

@[expose] def dualChecks : List Bool :=
  [relOK, dualRowsLenOK, dualPLenOK, dualCombLenOK, dualCombOK]

@[expose] def dualOK : Bool := dualChecks.all id

@[expose] def gamma0 : Nat := ofWords cocycleSplitGamma0

@[expose] def xmask : List Nat := cocycleSplitX.map ofWords

@[expose] def emask : Nat := ofWords cocycleSplitE

@[expose] def combSplit : List Nat := cocycleSplitComb.map ofWords

@[expose] def preMask (k rho v : Nat) : Nat :=
  ten.foldr
    (fun b acc => if v.testBit b then (2 ^ (100 * k + 10 * b + rho)) ^^^ acc else acc) 0

@[expose] def preMaskVec (k v : Nat) : List Nat :=
  ten.map fun rho => preMask k rho v

@[expose] def rowStep (k : Nat) (first tail : List Nat) : List Nat :=
  ten.map fun rho =>
    first[rho]! ^^^
      ten.foldr
        (fun rhop acc => if (gl k (2 ^ rhop)).testBit rho then tail[rhop]! ^^^ acc else acc) 0

@[expose] def rowAll : List Nat → Nat → List Nat
  | [], _ => List.replicate 10 0
  | k :: w, j => rowStep k (preMaskVec k (wordAct w (2 ^ j))) (rowAll w j)


@[expose] def splitRows : List Nat :=
  rels.flatMap fun r => (List.range 10).flatMap fun j => rowAll r j

@[expose] def cobMask1 (k b rho : Nat) : Nat :=
  ten.foldr
    (fun p acc => if (gl k (2 ^ b)).testBit p then xmask[10 * p + rho]! ^^^ acc else acc) 0

@[expose] def cobMask2 (k b rho : Nat) : Nat :=
  ten.foldr
    (fun q acc => if (gl k (2 ^ q)).testBit rho then xmask[10 * b + q]! ^^^ acc else acc) 0

@[expose] def cobMask (k b rho : Nat) : Nat := cobMask1 k b rho ^^^ cobMask2 k b rho

@[expose] def unitMask (k b rho : Nat) : Nat := 2 ^ (100 * k + 10 * b + rho)

@[expose] def splitRes (u : Nat) : Nat :=
  unitMask (u / 100) ((u / 10) % 10) (u % 10) ^^^
    cobMask (u / 100) ((u / 10) % 10) (u % 10) ^^^
    (if gamma0.testBit u then emask else 0)

@[expose] def gcol (k b : Nat) : Nat :=
  ten.foldr
    (fun rho acc => if gamma0.testBit (100 * k + 10 * b + rho) then (2 ^ rho) ^^^ acc else acc) 0

@[expose] def dot (a b : Nat) : Nat :=
  (List.range 300).foldl (fun acc i => if a.testBit i && b.testBit i then acc ^^^ 1 else acc) 0

@[expose] def fixT : Bool := (gl 0 1 == 1) && (gl 1 1 == 1)

@[expose] def noW : Bool :=
  (List.range 1024).all fun w =>
    !((gcol 0 0 == (w ^^^ gl 0 w)) && (gcol 1 0 == (w ^^^ gl 1 w)))

@[expose] def splitRowsLenOK : Bool := splitRows.length == 2500

@[expose] def xmaskLenOK : Bool := xmask.length == 100

@[expose] def combSplitLenOK : Bool := combSplit.length == 300

@[expose] def gamma0LenOK : Bool := decide (gamma0 < 2 ^ 300)

@[expose] def splitSolOK : Bool :=
  (List.range 2500).all (fun i => dot (splitRows[i]!) gamma0 == 0)

@[expose] def splitMaskOK : Bool :=
  (List.range 300).all fun u =>
    xorRowsByMask splitRows (combSplit[u]!) == splitRes u

@[expose] def splitChecks : List Bool :=
  [splitRowsLenOK, xmaskLenOK, combSplitLenOK, gamma0LenOK, fixT,
    splitSolOK, noW, splitMaskOK]

@[expose] def splitOK : Bool := splitChecks.all id

@[expose] def cocycleChecks : List Bool := [dualOK, splitOK]

@[expose] def cocycleOK : Bool := cocycleChecks.all id

end CFSG.Sporadic.Co2Jc.Native
