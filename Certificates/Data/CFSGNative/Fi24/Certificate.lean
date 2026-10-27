module

public import Certificates.Data.CFSGNative.Fi24.Data
public import Certificates.Data.CFSGNative.Fi24.Verify
public import Certificates.Data.CFSGNative.Fi24.Sep
public import Certificates.Data.CFSGNative.Fi23.Slp
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

set_option compiler.extract_closed false

@[expose] def decode81 (s : String) : Array Nat := Id.run do
  let ds := digits81.toList
  let tbl : Array Nat := (Array.range 128).map fun c => ds.idxOf (Char.ofNat c)
  let mut out : Array Nat := Array.mkEmpty (4 * s.length)
  for ch in s.toList do
    let x := tbl[ch.toNat]?.getD 0
    out := ((((out.push (x % 3)).push (x / 3 % 3)).push (x / 9 % 3)).push (x / 27 % 3))
  return out

@[expose] def nPts (_ : Unit := ()) : Nat := 306936

@[expose] def matA (_ : Unit := ()) : Array W := rowsOfSeed 781 seedA

@[expose] def matB (_ : Unit := ()) : Array W := rowsOfSeed 781 seedB

@[expose] def matAT (_ : Unit := ()) : Array W := transposeW 781 781 matA

@[expose] def matBT (_ : Unit := ()) : Array W := transposeW 781 781 matB

@[expose] def matF (_ : Unit := ()) : Array W :=
  let e := decode81 formData
  Array.ofFn (n := 781) fun i => ofTrits 781 fun j => e[781 * i.val + j]?.getD 0

@[expose] def initRows (_ : Unit := ()) : Array W :=
  let e := decode81 initData
  Array.ofFn (n := 253) fun i => ofTrits 781 fun j =>
    if j < 253 then (if j = i.val then 1 else 0) else e[528 * i.val + (j - 253)]?.getD 0

@[expose] def gensT (_ : Unit) : Gens := ⟨frTable matAT, frTable matBT⟩

@[expose] def rootForm (_ : Unit := ()) : RRef := rref 781 initRows

@[expose] def matrixChecks (_ : Unit) : Bool :=
  canonRows 781 matA && canonRows 781 matB && canonRows 781 matF &&
    eqRows 781 (mulW matA matA) (idW 781) &&
    eqRows 781 (mulW matB (mulW matB matB)) (idW 781) &&
    eqRows 781 (powW 781 (mulW matA matB) 29) (idW 781) &&
    !eqRows 781 matA (idW 781) && !eqRows 781 matB (idW 781) &&
    !eqRows 781 (mulW matA matB) (idW 781) &&
    eqRows 781 (mulW (mulW matAT matF) matA) matF &&
    eqRows 781 (mulW (mulW matBT matF) matB) matF

@[expose] def orbitData (_ : Unit) : Enum := enumOrbit gensT rootForm.rows 100 4096 3

@[expose] def genTables (O : Enum) (z : Int) : Table :=
  if z = 1 ∨ z = -1 then O.alpha else if z = 2 then O.beta else invT nPts O.beta

@[expose] def chainLetters (O : Enum) : Array Table := slpLetters nPts (genTables O) chainWords

@[inline, expose] def inTreeB (T : Tree) (p : Nat) : Bool :=
  ap T.pos p < T.pts.size && ap T.pts (ap T.pos p) == p

@[expose] def actionChecks (O : Enum) (chunks : Nat) : Bool :=
  let L := chainLetters O
  let T := chainTrees nPts L chainBase
  let lv1 := levelLetters L chainBase 1
  let T2 := treeBFS nPts subRoot L lv1
  invOK nPts O.beta (invT nPts O.beta) &&
    slpOK chainWords && chainWords.size == 13 && chainWords[0]! == [1] && chainWords[1]! == [2] &&
    chainOK nPts L chainBase chainBase chainQb T chunks &&
    orbitSizes T == [306936, 275264, 218400, 93312, 243, 3] &&
    treeOK nPts subRoot T2 L lv1 && T2.pts.size == 31671 &&
    allIn 0 nPts (fun p => p == 0 || inTreeB T[1]! p || inTreeB T2 p)

@[expose] def baseForms (O : Enum) : Array (Array W) :=
  chainBase.map fun b => (formAt gensT O rootForm b).rows

@[expose] def sepChecks (O : Enum) : Bool :=
  let Rs := baseForms O
  let Ks := Rs.map fun R => gramW 253 R matF
  let Ss := Ks.map (invW 253)
  let Zs := (Array.range 6).map fun h => orthoProj 253 Rs[h]! matF Ss[h]!
  let v := ofTrits 781 fun j => (decode81 sepVecData)[j]?.getD 0
  let w := combW 781 Zs sepTerms
  let P := sepP w v sepK
  let S := spinW (Zs.map fun M => frTable (transposeW 781 781 M)) v sepTree
  let Tinv := invW 781 S
  (Array.range 6).all (fun h => canonRows 253 Ss[h]! && eqRows 253 (mulW Ss[h]! Ks[h]!) (idW 253) &&
      eqRows 253 (mulW Ks[h]! Ss[h]!) (idW 253)) &&
    sepOKW Zs sepTerms v sepK P Tinv sepTree

@[expose] def fi24Certificate (chunks : Nat) : Bool :=
  matrixChecks () &&
    let O := orbitData ()
    orbitVerify gensT O rootForm nPts chunks && actionChecks O chunks && sepChecks O

end CFSG.Sporadic.Fi24.Native
