module

public import Certificates.Data.CFSGNative.HN.F5Orbit
public import Certificates.Data.CFSGNative.HN.LevelChain
public import Certificates.Data.CFSGNative.He.Fp
public import Certificates.Data.CFSGNative.Fi23.Slp
public import Certificates.Data.CFSGNative.HS.Cert

public section

namespace CFSG.Sporadic.F5.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.LevelChain.Native
open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.He.Native
open CFSG.Sporadic.SmallF2.Native (labelsOf inTreeB ordOK)

set_option compiler.extract_closed false

structure F5Data where
  d : Nat
  seedA : String
  seedB : String
  expA : Nat
  expB : Nat
  root : String
  n : Nat
  Q : Array Nat
  base : Array Nat
  qb : Array Nat
  starts : Array Nat
  words : Array (List Int)
  ords : Array Nat
  orbSizes : List Nat
  subReps : Array Nat
  subSizes : List Nat
  ordA : Nat × Nat
  ordB : Nat × Nat
  gWord : List Int
  ordC : Nat × Nat
  suppliedOrbit : Option (Unit → VOrbit) := none

namespace F5Data

variable (D : F5Data)

@[expose] def rowsA : Array (Array Nat) := rowsOf 5 D.d D.seedA

@[expose] def rowsB : Array (Array Nat) := rowsOf 5 D.d D.seedB

@[expose] def tabA (_ : Unit) : Array W17 := frTable D.d D.d D.rowsA

@[expose] def tabB (_ : Unit) : Array W17 := frTable D.d D.d D.rowsB

@[expose] def v0 : ByteArray := bytesOfDigits D.root

@[expose] def orbit (_ : Unit) : VOrbit :=
  match D.suppliedOrbit with
  | some getOrbit => getOrbit ()
  | none => f5OrbitBFS D.d (D.tabA ()) (D.tabB ()) D.v0 D.n

end F5Data

@[expose] def genT (n : Nat) (O : VOrbit) (z : Int) : Table :=
  if z = 1 then O.alpha else if z = -1 then invT n O.alpha else if z = 2 then O.beta
  else invT n O.beta

@[expose] def invWord (w : List Int) : List Int := w.reverse.map (- ·)

@[expose] def cWordOf (g : List Int) : List Int := [1] ++ invWord g ++ [2] ++ g

@[expose] def maskSum (sizes : List Nat) (mask : Nat) : Nat :=
  Nat.fold sizes.length (fun i _ acc => if mask.testBit i then acc + sizes[i]! else acc) 0

@[expose] def divOK (n : Nat) (sizes : List Nat) : Bool :=
  allIn 0 (2 ^ (sizes.length - 1)) fun m =>
    !(n % maskSum sizes (2 * m + 1) == 0) || 2 * m + 1 == 1 || 2 * m + 1 == 2 ^ sizes.length - 1

@[expose] def matrixChecks (D : F5Data) : Bool :=
  decide (0 < D.d) && decide (D.d ≤ 135) && decide (0 < D.expA) && decide (0 < D.expB) &&
    powM 5 D.d D.rowsA D.expA == idM D.d && powM 5 D.d D.rowsB D.expB == idM D.d

@[expose] def basisCheck (D : F5Data) (O : VOrbit) : Bool :=
  let M := colsMat D.d (D.Q.map fun q => bytesToNats O.keys[q]!)
  mulM 5 D.d M (invM 5 D.d M) == idM D.d

@[expose] def orbitChecks (D : F5Data) (O : VOrbit) (chunks : Nat) : Bool :=
  f5OrbitOK D.d (D.tabA ()) (D.tabB ()) D.v0 O chunks && O.keys.size == D.n &&
    O.alpha.size == D.n && O.beta.size == D.n && decide (D.n < 2 ^ 30) &&
    invOK D.n O.alpha (invT D.n O.alpha) && invOK D.n O.beta (invT D.n O.beta) &&
    decide (D.d ≤ D.Q.size) && D.Q.all (· < D.n) && basisCheck D O

@[expose] def chainChecks (D : F5Data) (L : Array Table) (T : Array Tree) (chunks : Nat) : Bool :=
  slpOK D.words && nestOK D.words D.starts && D.starts.size == D.base.size + 1 &&
    decide (2 ≤ D.base.size) && D.base[0]! == 0 &&
    levelChainOK D.n L D.starts D.ords D.base D.Q D.qb T chunks && T[0]!.pts.size == D.n &&
    orbitSizes T == D.orbSizes

@[expose] def subChecks (D : F5Data) (L : Array Table) (lv : Array Nat) (S : Array Tree) :
    Bool :=
  let k := D.subReps.size
  let labs := labelsOf D.n S
  decide (0 < k) && D.subReps[0]! == 0 && S.size == k &&
    (S.toList.map fun T => T.pts.size) == D.subSizes &&
    allIn 0 k (fun j => treeOK D.n D.subReps[j]! S[j]! L lv) &&
    allIn 0 D.n (fun p => decide (labs[p]! < k) && inTreeB S[labs[p]!]! p) &&
    allIn 0 k (fun j => allIn 0 S[j]!.pts.size fun t => labs[ap S[j]!.pts t]! == j) &&
    divOK D.n D.subSizes

@[expose] def ordChecks (D : F5Data) (O : VOrbit) : Bool :=
  ordOK D.n D.Q O.alpha D.ordA && ordOK D.n D.Q O.beta D.ordB &&
    ordOK D.n D.Q (wordT D.n (genT D.n O) (cWordOf D.gWord)) D.ordC

@[expose] def f5Cert (D : F5Data) (chunks : Nat) : Bool :=
  matrixChecks D && (
    let O := D.orbit ()
    orbitChecks D O chunks && (
      let L := slpLetters D.n (genT D.n O) D.words
      let T := levelTrees D.n L D.starts D.base
      let lv := levelLv D.starts 1
      let S := D.subReps.map fun r => treeBFS D.n r L lv
      chainChecks D L T chunks && subChecks D L lv S && ordChecks D O))

end CFSG.Sporadic.F5.Native
