module

public import Certificates.Data.CFSGNative.Ly.Orbit
public import Certificates.Data.CFSGNative.Ly.Faith
public import Certificates.Data.CFSGNative.Ly.Data
public import Certificates.Data.CFSGNative.Fi23.Slp
public import Certificates.Data.CFSGNative.Perm.Chain
public import Certificates.Data.CFSGNative.HN.LevelChain

public section

namespace CFSG.Sporadic.Ly.Native

open CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.LevelChain.Native

set_option compiler.extract_closed false

@[expose] def nPts (_ : Unit := ()) : Nat := 8835156

@[expose] def matA (_ : Unit := ()) : Array (Array Nat) := rowsOf 5 111 seedA

@[expose] def matB (_ : Unit := ()) : Array (Array Nat) := rowsOf 5 111 seedB

@[expose] def tabA (_ : Unit := ()) : Array W14 := frTable matA

@[expose] def tabB (_ : Unit := ()) : Array W14 := frTable matB

@[expose] def rootDigitArr (_ : Unit := ()) : Array Nat := digitsOf rootDigits

@[expose] def rootKey (_ : Unit := ()) : ByteArray :=
  encodeDigits fun p => if p < 826 then rootDigitArr[p]! else 0

@[expose] def formF (_ : Unit := ()) : Array (Array Nat) := matOfDigits formDigits

@[expose] def orbitData (_ : Unit) : KOrbit := bfsPar tabA tabB rootKey nPts 4096 4

@[expose] def matG (_ : Unit := ()) : Array (Array Nat) :=
  let t := mulM 5 111 matA (powM 5 111 matB 4)
  mulM 5 111 t t

@[expose] def matGi (_ : Unit := ()) : Array (Array Nat) :=
  let t := mulM 5 111 matB matA
  mulM 5 111 t t

@[expose] def matX (_ : Unit := ()) : Array (Array Nat) :=
  mulM 5 111 (mulM 5 111 (mulM 5 111 matA matGi) matB) matG

@[expose] def matrixChecks (_ : Unit) : Bool :=
  mulM 5 111 matA matA == idM 111 && powM 5 111 matB 5 == idM 111 &&
    powM 5 111 matX 67 == idM 111 &&
    mulM 5 111 (transM matA) (mulM 5 111 formF matA) == formF &&
    mulM 5 111 (transM matB) (mulM 5 111 formF matB) == formF

@[expose] def keyRows (key : ByteArray) : Array ByteArray :=
  Array.ofFn (n := 7) fun m =>
    ⟨Array.ofFn (n := 112) fun j => UInt8.ofNat (keyDigit key (111 * m.val + j.val))⟩

@[expose] def rootChecks (_ : Unit) : Bool :=
  rootKey.size == 276 && allIn 0 276 (fun q => (rootKey.get! q).toNat < 125) &&
    rrefOK (keyRows rootKey) #[0, 1, 2, 3, 4, 5, 6] &&
    mul7 (keyS rootKey) (inv7 (keyS rootKey)) == id7

@[expose] def genTables (alpha beta : Table) (z : Int) : Table :=
  if z = 1 ∨ z = -1 then alpha else if z = 2 then beta else invT nPts beta

@[expose] def chainLetters (alpha beta : Table) : Array Table :=
  slpLetters nPts (genTables alpha beta) chainWords

@[inline, expose] def inTreeB (T : Tree) (p : Nat) : Bool :=
  decide (ap T.pos p < T.pts.size) && ap T.pts (ap T.pos p) == p

@[expose] def labelsOf (subT : Array Tree) : Array Nat := Id.run do
  let mut labs : Array Nat := Array.replicate nPts 0
  for j in [0:subT.size] do
    let T := subT[j]!
    for k in [0:T.pts.size] do
      labs := labs.set! (ap T.pts k) j
  return labs

@[expose] def subChecks (L : Array Table) (lv : Array Nat) (S : Array Tree) (labs : Array Nat) :
    Bool :=
  let k := subReps.size
  S.size == k && (S.toList.map fun T => T.pts.size) == subSizes &&
    allIn 0 k (fun j => treeOK nPts subReps[j]! S[j]! L lv) &&
    allIn 0 nPts (fun p => decide (labs[p]! < k) && inTreeB S[labs[p]!]! p) &&
    allIn 0 k (fun j => allIn 0 S[j]!.pts.size fun t => labs[ap S[j]!.pts t]! == j)

@[expose] def iterT (T : Table) : Nat → Array Nat → Array Nat
  | 0, q => q
  | e + 1, q => apT T (iterT T e q)

@[expose] def ordQ (T : Table) (p : Nat) : Bool :=
  tupleEq (iterT T p chainQ) chainQ && !tupleEq (apT T chainQ) chainQ

@[expose] def actionChecks (alpha beta : Table) : Bool :=
  let L := chainLetters alpha beta
  let T := levelTrees nPts L chainStarts chainBase
  let lv := levelLv chainStarts 1
  let S := subReps.map fun r => treeBFS nPts r L lv
  let labs := labelsOf S
  alpha.size == nPts && beta.size == nPts && invoOK nPts alpha &&
    invOK nPts beta (invT nPts beta) && slpOK chainWords && nestOK chainWords chainStarts &&
    chainStarts.size == 4 &&
    levelChainOK nPts L chainStarts chainOrds chainBase chainQ chainQb T 3 &&
    orbitSizes T == [8835156, 2034375, 2880] && chainBase[0]! == 0 && subReps[0]! == 0 &&
    subChecks L lv S labs && ordQ alpha 2 && ordQ beta 5 &&
    ordQ (compT nPts alpha (wordT nPts (genTables alpha beta) conjWord)) 67

@[expose] def qKeys (O : KOrbit) : Array ByteArray := chainQ.map fun q => O.keys[q]!

@[expose] def orbitPart (O : KOrbit) : Bool :=
  orbitOK tabA tabB rootKey O 3 && O.keys.size == nPts &&
    faithChecks (qKeys O) formF (matOfDigits faithY) (matOfDigits faithCinv) (digitsOf faithV)
      (digitsOf faithW) faithPar faithOp faithAB faithMu &&
    actionChecks O.alpha O.beta

@[expose] def lyCertificate (_ : Unit) : Bool :=
  matrixChecks () && rootChecks () && orbitPart (orbitData ())

end CFSG.Sporadic.Ly.Native
