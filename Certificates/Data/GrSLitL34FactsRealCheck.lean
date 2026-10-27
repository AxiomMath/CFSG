module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
public import Certificates.Data.GrSLitL34FactsRealReps
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Open.Defs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def rTab (w : List ℕ) : Tab := w.foldl (fun t j => comp 42 t gTabs[j]!) (idTab 42)

@[expose] def repTab (i : ℕ) : Tab := rTab (realRepWords.getD i [])

@[expose] def uA (i : ℕ) : List (Fin 2 × Bool) := parseWord (realRepU.getD i ("", "")).1

@[expose] def uB (i : ℕ) : List (Fin 2 × Bool) := parseWord (realRepU.getD i ("", "")).2

@[expose] def aut (i : ℕ) : List (List (Fin 2 × Bool)) := autWs (uA i) (uB i)

@[expose] def zOf (e : ℕ × ℕ × ℕ × ℕ) : List (Fin 2 × Bool) := zword e.2.1 e.2.2.1 e.2.2.2

@[expose] def t1Walk (k l : ℕ) : List (Fin 2 × Bool) :=
  FreeGroup.invRev (zOf (t1Entry k l)) ++ FreeGroup.invRev (tw (t1Entry k l).1) ++ tw k ++ tw l

@[expose] def alphaWalk (i k : ℕ) : List (Fin 2 × Bool) :=
  FreeGroup.invRev (zOf (alphaEntry i k)) ++ FreeGroup.invRev (tw (alphaEntry i k).1) ++
    substWord (aut i) (tw k)

@[expose] def zGen (j : ℕ) : List (Fin 2 × Bool) := if j = 0 then zOne else zTwo

@[expose] def alphaZWalk (i j : ℕ) : List (Fin 2 × Bool) :=
  FreeGroup.invRev (zOf (alphaEntry i (64 + j))) ++ substWord (aut i) (zGen j)

@[expose] def realWalks : List (List (Fin 2 × Bool) × ℕ) :=
  ((List.range 64).flatMap fun k => (List.range 64).map fun l => (t1Walk k l, 1)) ++
    ((List.range 36).flatMap fun i => (List.range 64).map fun k => (alphaWalk i k, 1)) ++
    ((List.range 36).flatMap fun i => (List.range 2).map fun j => (alphaZWalk i j, 1))

@[expose] def entryOK (e : ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (e.1 < 64) && decide (e.2.1 < 4) && decide (e.2.2.1 < 4) && decide (e.2.2.2 < 3)

@[expose] def invOKR (x : Tab) : Bool :=
  (invTab 42 x).size == 42 && comp 42 (invTab 42 x) x == idTab 42

@[noinline, expose] def realSigmaOK : Bool :=
  allBelow 64 (fun k => allBelow 64 fun l => entryOK (t1Entry k l) &&
    comp 42 (wordTab (tg k)) (wordTab (tg l)) == wordTab (tg (t1Entry k l).1)) &&
  allBelow 36 fun i =>
    let g := repTab i
    let gi := invTab 42 g
    invOKR g && abTab (uA i) == conjTab 42 g gi aST && abTab (uB i) == conjTab 42 g gi bST &&
      (allBelow 64 fun k => entryOK (alphaEntry i k) &&
        conjTab 42 g gi (wordTab (tg k)) == wordTab (tg (alphaEntry i k).1)) &&
      entryOK (alphaEntry i 64) && (alphaEntry i 64).1 == 0 &&
      entryOK (alphaEntry i 65) && (alphaEntry i 65).1 == 0

@[noinline, expose] def realDecompOK : Bool :=
  let ER := enumBFS 42 gTabs 241920
  let ET := enumBFS 42 (wordTabs wT₀) 64
  let idx := indexOf ET.tabs
  let ri := (Array.range 36).map fun i => invTab 42 (repTab i)
  allBelow ER.tabs.size fun k =>
    let y := ER.tabs[k]!
    (invOKR y && anyBelow 4 fun j => notInOK ET.tabs (conjTab 42 y (invTab 42 y) (wordTabs wT₀)[j]!)) ||
      anyBelow 36 fun i => found idx ET.tabs (comp 42 y ri[i]!)

@[noinline, expose] def realModelOK : Bool :=
  orderCheck coverWs [1] 20 3000000 193536 realWalks 100 && realSigmaOK && realDecompOK

end CFSG.ComponentClassification.GrSLit.L34Facts.Real
