
module

public import CFSG.Monster.B.TwoA.Fischer.CertFixedBase
public meta import CFSG.Monster.B.TwoA.Fischer.CertFixedBase
public meta import Certificates.Data.CFSGNative.MonsterB.BinaryRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary CFSG.Monster.B.Binary.Native
open scoped Matrix

@[expose] def tableEntryOK (lab : Array ℕ) (i j : ℕ) : Bool :=
  bTable i j == if lab[basisPt j]! = basisPt j then 0
    else labelCoord (basisPt i) ^^^ labelCoord (basisPt j) ^^^ labelCoord lab[basisPt j]!

@[expose] def tableRowOK (i : ℕ) : Bool :=
  let lab := jLabelArr (labelWord i)
  (List.range 78).all fun j => tableEntryOK lab i j

@[expose] def tableCheck : Bool :=
  bTableArr.size == 78 && bTableArr.all (·.size == 78) && (List.range 78).all tableRowOK

@[expose] def tableCol (c : ℕ) : Array ℕ := Array.ofFn (n := 78) fun i => bTable i c

@[expose] def adCols (m : ℕ) : Array ℕ := Array.ofFn (n := 78) fun c => vecMulN 78 (tableCol c) m

@[expose] def transIdx : List ℕ := (List.range 10).map (· + 2)

@[expose] def radicalCheck : Bool :=
  ((List.range 22).all fun c => decide (labelCoord c < 2 ^ 11)) &&
    ((List.range 11).all fun q => decide (basisPt q < 22)) &&
    (transIdx.all fun k => (List.range 2048).all fun m => vecMulN 78 (fColArr[k]!) m == m) &&
    (transIdx.all fun k => (List.range 11).all fun q => fCol k q == 2 ^ q)

@[expose] def orbitData : Array ℕ × Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut idx : Array ℕ := Array.replicate 2048 2048
  let mut dist : Array ℕ := Array.replicate 2048 0
  let mut par : Array ℕ := Array.replicate 2048 0
  let mut gen : Array ℕ := Array.replicate 2048 0
  let mut t := 0
  for s in [0:2048] do
    if idx[s]! == 2048 then
      idx := idx.set! s t
      let mut queue : Array ℕ := #[s]
      let mut h := 0
      for _ in [0:2048] do
        if h < queue.size then
          let u := queue[h]!
          for k in [0:2] do
            let x := vecMulN 78 (fColArr[k]!) u
            if x < 2048 && idx[x]! == 2048 then
              idx := idx.set! x t
              dist := dist.set! x (dist[u]! + 1)
              par := par.set! x u
              gen := gen.set! x k
              queue := queue.push x
          h := h + 1
      t := t + 1
  return (idx, dist, par, gen)

@[expose] def orbIdx (m : ℕ) : ℕ := orbitData.1[m]!

@[expose] def orbDist (m : ℕ) : ℕ := orbitData.2.1[m]!

@[expose] def orbPar (m : ℕ) : ℕ := orbitData.2.2.1[m]!

@[expose] def orbGen (m : ℕ) : ℕ := orbitData.2.2.2[m]!

@[expose] def orbRep (t : ℕ) : ℕ := [0, 1, 3, 7, 39, 117, 437, 949][t]!

@[expose] def orbLen (t : ℕ) : ℕ := [1, 22, 231, 770, 770, 231, 22, 1][t]!

@[expose] def orbRank (t : ℕ) : ℕ := [0, 22, 32, 38, 38, 32, 22, 22][t]!

@[expose] def orbitEntryOK (m : ℕ) : Bool :=
  decide (orbIdx m < 8) &&
    ((List.range 12).all fun k =>
      let x := vecMulN 78 (fColArr[k]!) m
      decide (x < 2048) && orbIdx x == orbIdx m) &&
    (if orbDist m = 0 then m == orbRep (orbIdx m)
      else decide (orbPar m < 2048) && orbIdx (orbPar m) == orbIdx m &&
        orbDist (orbPar m) + 1 == orbDist m && decide (orbGen m < 2) &&
        vecMulN 78 (fColArr[orbGen m]!) (orbPar m) == m) &&
    spanRankIs 78 (adCols m).toList (orbRank (orbIdx m))

@[expose] def orbitCheck : Bool :=
  ((List.range 2048).all orbitEntryOK) &&
    ((List.range 8).all fun t => orbIdx (orbRep t) == t && decide (orbRep t < 2048)) &&
    (List.range 2048).all fun m =>
      (orbIdx m == 0) == (m == 0) && (orbIdx m == 7) == (m == 949) &&
        (orbIdx m == 1) == ((List.range 22).map labelCoord).contains m &&
        (orbIdx m == 6) == ((List.range 22).map fun c => 949 ^^^ labelCoord c).contains m

@[expose] def zeroSetOK (u : ℕ) : Bool :=
  let a := adCols u
  (List.range 3510).all fun q =>
    let b := vecMulN 78 a (labelCoord q)
    decide (b < 2 ^ 78) && (b == 0) == decide (q < 22)

@[expose] def zeroSetCheck : Bool :=
  zeroSetOK 949 && (List.range 22).all fun c => zeroSetOK (949 ^^^ labelCoord c)

end CFSG.Monster.B.TwoA.Fischer.Cert
