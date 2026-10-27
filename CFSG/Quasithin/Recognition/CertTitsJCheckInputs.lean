module

public import Std.Data.HashMap
public import CFSG.Sporadic.Schreier.TitsStabCheck
public import CFSG.Quasithin.Recognition.CertTitsEnum4
public import CFSG.Quasithin.Recognition.CertVertexTable
public meta import Std.Data.HashMap
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsStabCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Quasithin.Recognition.CertTitsEnum4
public meta import CFSG.Quasithin.Recognition.CertVertexTable
public import CFSG.Foundations
public meta import CFSG.Foundations
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public meta import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public meta import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.A1bGroups
public meta import CFSG.Quasithin.Background.A1bGroups
public meta import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public meta import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Sporadic.Schreier.TitsChain
public meta import CFSG.Sporadic.Schreier.TitsChain

public section

namespace CFSG.Quasithin

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def jLevels : Array Level := rawLevels 1755 titsJArrs (baseArr 1755 titsJBase)

@[expose] def jPel : Array (Array ℕ) := table4 1755 jLevels

@[expose] def jKey4 (x0 x1 x2 x3 : ℕ) : ℕ := ((x0 * 1755 + x1) * 1755 + x2) * 1755 + x3

@[expose] def jIdxMap : Std.HashMap ℕ ℕ :=
  (List.range jPel.size).foldl
    (fun m i => m.insert (jKey4 (jPel[i]!)[5]! (jPel[i]!)[1]! (jPel[i]!)[24]! (jPel[i]!)[12]!) i) {}

@[expose] def jIdx4 (x0 x1 x2 x3 : ℕ) : ℕ := jIdxMap.getD (jKey4 x0 x1 x2 x3) 0

@[expose] def jIdx (a : Array ℕ) : ℕ := jIdx4 a[5]! a[1]! a[24]! a[12]!

@[expose] def jMulT : Array (Array ℕ) :=
  Array.ofFn (n := 512) fun i => Array.ofFn (n := 512) fun j =>
    jIdx4 (jPel[i]!)[(jPel[j]!)[5]!]! (jPel[i]!)[(jPel[j]!)[1]!]! (jPel[i]!)[(jPel[j]!)[24]!]!
      (jPel[i]!)[(jPel[j]!)[12]!]!

@[expose] def jInvT : Array ℕ := Array.ofFn (n := 512) fun i => jIdx (invCand 1755 jPel[i]!)

@[expose] def jOneI : ℕ := jIdx (idA 1755)

@[expose] def jZArr : Array ℕ := wordArr 1755 titsDerivedArrs titsCenterWord

@[expose] def jZI : ℕ := jIdx jZArr

@[expose] def jOps : VOps 512 where
  mul i j := finPt 512 (jMulT[(i : ℕ)]!)[(j : ℕ)]!
  inv i := finPt 512 jInvT[(i : ℕ)]!
  one := finPt 512 jOneI
  zI := finPt 512 jZI

@[expose] def jEBarr : Array Bool := Array.ofFn (n := 512) fun i =>
  decide (∀ j : Fin 512, jOps.comm i j = jOps.one ∨ jOps.comm i j = jOps.zI)

@[expose] def jEB (i : Fin 512) : Bool := jEBarr[(i : ℕ)]!

@[expose] def jFBarr : Array Bool := Array.ofFn (n := 512) fun i =>
  decide (∀ e : Fin 512, jEB e = true → jOps.mul i e = jOps.mul e i)

@[expose] def jFB (i : Fin 512) : Bool := jFBarr[(i : ℕ)]!

@[expose] def jGenArrs : Array (Array ℕ) :=
  (titsHWords.map fun w => wordArr 1755 titsDerivedArrs w).toArray

@[expose] def jGenInvArrs : Array (Array ℕ) := jGenArrs.map (invCand 1755)

@[expose] def jCjT : Array (Array ℕ) :=
  Array.ofFn (n := 3) fun k => Array.ofFn (n := 512) fun i =>
    jIdx (compA 1755 (compA 1755 jGenArrs[(k : ℕ)]! jPel[i]!) jGenInvArrs[(k : ℕ)]!)

@[expose] def jCj (k : Fin 3) (i : Fin 512) : Fin 512 := finPt 512 (jCjT[(k : ℕ)]!)[(i : ℕ)]!

@[expose] def jC0Arr : Array ℕ := wordArr 1755 titsDerivedArrs [3, 4, 13]

@[expose] def jCArr : Array ℕ := compA 1755 jC0Arr jC0Arr

@[expose] def jCInv : Array ℕ := invCand 1755 jCArr

@[expose] def jCcT : Array ℕ :=
  Array.ofFn (n := 512) fun i => jIdx (compA 1755 (compA 1755 jCArr jPel[i]!) jCInv)

@[expose] def jCc (i : Fin 512) : Fin 512 := finPt 512 jCcT[(i : ℕ)]!

@[expose] def jI0N : ℕ :=
  ((List.range 512).find? fun i => !(jFBarr[i]!) && (jMulT[i]!)[i]! == jOneI).getD 0

@[expose] def jBfs : Array ℕ × Array ℕ := Id.run do
  let mut par : Array ℕ := Array.replicate 512 512
  let mut gl : Array ℕ := Array.replicate 512 0
  let mut queue : Array ℕ := #[jI0N]
  par := par.set! jI0N jI0N
  let mut head := 0
  for _ in [0:512] do
    if head < queue.size then
      let x := queue[head]!
      head := head + 1
      for k in [0:3] do
        let y := (jCjT[k]!)[x]!
        if par[y]! == 512 then
          par := par.set! y x
          gl := gl.set! y k
          queue := queue.push y
  return (par, gl)

@[expose] def jWordAux (par gl : Array ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, j =>
    if j == jI0N then [] else if par[j]! == 512 then [] else gl[j]! :: jWordAux par gl fuel par[j]!

@[expose] def jWtab (j : Fin 512) : List (Fin 3) :=
  (jWordAux jBfs.1 jBfs.2 600 (j : ℕ)).map (finPt 3)

@[expose] def jI0 : Fin 512 := finPt 512 jI0N

end CFSG.Quasithin
