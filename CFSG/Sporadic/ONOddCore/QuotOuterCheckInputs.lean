module

public import CFSG.Sporadic.ONOddCore.LocalAutPayload
public import CFSG.Sporadic.ONOddCore.SigmaTriple
public import CFSG.Sporadic.ONOddCore.GraphDefs
public import CFSG.Sporadic.Schreier.ONCheckSmallAux
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public meta import CFSG.Sporadic.ONOddCore.LocalAutPayload
public meta import CFSG.Sporadic.ONOddCore.SigmaTriple
public meta import CFSG.Sporadic.ONOddCore.GraphDefs
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native

@[expose] def qgArr (j : Nat) : Array Nat := localCert.quotGens.getD j #[]

@[expose] def qiArr (r : QuotRecord) (j : Nat) : Array Nat := r.images.getD j #[]

@[expose] def xWords : Array (List Nat) :=
  #[[1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2], [1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2],
    [1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1], [2, 2, 2, 1, 2, 2, 1, 2, 1, 1, 1, 1],
    [2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2], [1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1],
    [2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1], [1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1],
    [1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1], [2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2],
    [1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1],
    [2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2]]

@[expose] def pairGens (r : QuotRecord) : Array Tab :=
  #[dbl 120 (qgArr 0) (qiArr r 0), dbl 120 (qgArr 1) (qiArr r 1)]

@[expose] def pairPosWords : Array (List Nat) :=
  #[[1, 2, 1, 1], [1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1], [1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1],
    [1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 2]]

@[expose] def pairDerWords : List (List Int) :=
  [[1, 2, 1, 1], [3, 3, 3], [-4, -1, -1, 4, 1], [-4, -5, -4, 5, 4, 5, 4]]

@[expose] def pairChainBaseL : List (Fin 240) := [0, 1, 2, 3]

@[expose] def pairChainBase : Array Nat := (pairChainBaseL.map Fin.val).toArray

@[expose] def pairStrongs (r : QuotRecord) : Array Tab :=
  pairGens r ++ pairPosWords.map (posArr 240 (pairGens r))

theorem pairGens_size (r : QuotRecord) : (pairGens r).size = 2 := rfl

theorem pairGens_get (r : QuotRecord) {j : ℕ} (hj : j < 2) :
    (pairGens r)[j]! = dbl 120 (qgArr j) (qiArr r j) := by
  interval_cases j <;> rfl

theorem pairStrongs_size (r : QuotRecord) : (pairStrongs r).size = 6 := by
  unfold pairStrongs
  rw [Array.size_append, Array.size_map]
  rfl

theorem pairStrongs_get (r : QuotRecord) :
    ∀ i < (pairGens r).size, (pairStrongs r)[i]! = (pairGens r)[i]! := by
  intro i hi
  have h2 : i < (pairStrongs r).size := by
    rw [pairStrongs_size]
    rw [pairGens_size] at hi
    omega
  rw [getElem!_pos (pairStrongs r) i h2, getElem!_pos (pairGens r) i hi]
  exact Array.getElem_append_left hi

theorem pairStrongs_word (r : QuotRecord) {j : ℕ} (hj : j < 4) :
    (pairStrongs r)[2 + j]! = posArr 240 (pairGens r) pairPosWords[j]! := by
  have hs : pairPosWords.size = 4 := rfl
  have h2 : 2 + j < (pairGens r ++ pairPosWords.map (posArr 240 (pairGens r))).size := by
    rw [Array.size_append, Array.size_map, pairGens_size, hs]
    omega
  change (pairGens r ++ pairPosWords.map (posArr 240 (pairGens r)))[2 + j]! = _
  rw [getElem!_pos (pairGens r ++ pairPosWords.map (posArr 240 (pairGens r))) (2 + j) h2,
    Array.getElem_append_right (by rw [pairGens_size]; omega)]
  have e : 2 + j - (pairGens r).size = j := by
    rw [pairGens_size]
    omega
  simp only [e, Array.getElem_map]
  rw [getElem!_pos pairPosWords j (by rw [hs]; exact hj)]

@[expose] def recordCheck (idx : Std.HashMap Tab Nat) (r : QuotRecord) : Bool :=
  allBelowN 2 (fun j => found idx m120Enum.tabs (pcomp 120 (pinvCand 120 Data.quotientConjugator)
    (pcomp 120 (qiArr r j) Data.quotientConjugator))) &&
    CFSG.Certificates.Native.rawChainOK 240 ((pairStrongs r).extract 0 2) (pairStrongs r)
      pairChainBase (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 6 pairDerWords) 1 &&
    (CFSG.Certificates.Native.rawOrbitSizes 240 (pairStrongs r) pairChainBase).prod == 40320 &&
    allBelowN 12 (fun m => peq 120 (posArr 120 #[qiArr r 0, qiArr r 1] xWords[m]!)
      (posArr 120 Data.PSL120Chain.generators (sigWord r.diag r.field r.graph m)))

@[noinline, expose] def quotCheck (idx : Std.HashMap Tab Nat) : Bool :=
  allBelowN 2 (fun j => peq 120 (qgArr j) (pcomp 120 Data.quotientConjugator
    (pcomp 120 Data.M120Chain.generators[j]! (pinvCand 120 Data.quotientConjugator)))) &&
    allBelowN 12 (fun m => peq 120 (posArr 120 #[qgArr 0, qgArr 1] xWords[m]!)
      Data.PSL120Chain.generators[m]!) &&
    xWords.all (fun w => w.all fun l => 1 ≤ l && l ≤ 2) &&
    localCert.records.all (recordCheck idx)

end CFSG.Sporadic.ONOddCore
