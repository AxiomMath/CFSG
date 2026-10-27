module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.O8Pi

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover (arrTable chainTables)

@[expose] def piIdx : List ℕ := [0, 2, 4, 6]

@[expose] def piGens (_ : Unit := ()) : Array (Array ℕ) := piIdx.toArray.map fun i => genArrs[i]!

@[expose] def piWords : List (List ℤ) := [[3, 2, 4, 2, 3, 2, 4], [2, 3, 2, 4, 2, 3, 4]]

@[expose] def piS (_ : Unit := ()) : Array (Array ℕ) := pushWords 360 (piGens ()) piWords

@[expose] def piBase : List (Fin 360) := [0, 4, 24, 8]

@[expose] def piChainCheck (S : Array (Array ℕ)) : Bool :=
  rawChainOK 360 (S.extract 0 4) S (piBase.map Fin.val).toArray (wordsOf 4 piWords) 4 &&
    rawOrbitSizes 360 S (piBase.map Fin.val).toArray == [64, 4, 4, 4]

@[expose] def testA (S : Array (Array ℕ)) : List (Array ℕ) :=
  let c₁ := wordA 360 S (rawInvs 360 S) [1, 2]
  let c₂ := wordA 360 S (rawInvs 360 S) [3, 6]
  [c₁, c₂, compA 360 (invCand 360 c₁) c₂]

@[expose] def testT (S : Array (Array ℕ)) : List (Table × Table) :=
  (testA S).map fun c => (arrTable 360 c, arrTable 360 (invCand 360 c))

@[expose] def baseN : List ℕ := [0, 4, 24, 8]

@[expose] def imgs (f : ℕ → ℕ) : List ℕ := baseN.map f

@[expose] def q8Imgs (x y : Table) : List (List ℕ) :=
  [imgs id, imgs (fun b => ap x (ap x b)), imgs (ap x), imgs (fun b => ap x (ap x (ap x b))),
    imgs (ap y), imgs (fun b => ap y (ap x (ap x b))), imgs (fun b => ap x (ap y b)),
    imgs (fun b => ap x (ap y (ap x (ap x b))))]

@[expose] def conjImg (c : Table × Table) (x : Table) : List ℕ :=
  imgs fun b => ap c.1 (ap x (ap c.2 b))

@[expose] def movesB (L : List (List ℕ)) (x y : Table) (c : Table × Table) : Bool :=
  !(L.contains (conjImg c x) && L.contains (conjImg c y))

@[expose] def presB (x y : Table) : Bool :=
  baseN.all fun b => ap y (ap x b) == ap x (ap x (ap x (ap y b)))

@[expose] def pairB (tests : List (Table × Table)) (x y : Table) : Bool :=
  !presB x y || tests.all (movesB (q8Imgs x y) x y)

@[expose] def sqMoves (T : Table) : Bool := (List.range 360).any fun i => ap T (ap T i) != i

@[expose] def sqKey (T : Table) : List ℕ := imgs fun b => ap T (ap T b)

@[expose] def sqList (S : Array (Array ℕ)) : List (Table × List ℕ) :=
  (filterProducts 360 sqMoves (chainTables 360 S (piBase.map Fin.val).toArray) (idT 360) []).map
    fun T => (T, sqKey T)

@[expose] def q8Check (S : Array (Array ℕ)) : Bool :=
  let tests := testT S
  let P := sqList S
  (P.map Prod.snd).dedup.all fun k =>
    let B := (P.filter fun p => p.2 == k).map Prod.fst
    B.all fun x => B.all fun y => pairB tests x y

@[expose] def check (_ : Unit := ()) : Bool :=
  let S := piS ()
  piChainCheck S && (testA S).all (fun c => isInvA 360 c (invCand 360 c)) && q8Check S

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.O8Pi
