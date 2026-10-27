module

public import Certificates.Data.GMS78RuQCheck
public import Certificates.Data.GMS78RuSimCheck
public import Certificates.Data.GMS78RuPi7Data
public import Certificates.Data.GMS78RuAsmData

public section

namespace CFSG.GMS78RuN

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.CosetTable
open CFSG.ComponentClassification.GMS78.RuPi7 CFSG.ComponentClassification.GMS78.RuAsm

@[expose] def nBasis : List Nat := [16, 48, 117, 222, 210, 243, 188, 20]

@[expose] def nCols : List Nat := [51, 255, 129, 153, 1, 3, 180, 90]

@[expose] def nB (j : Nat) : Nat := nBasis.getD j 0

@[expose] def nCo (m : Nat) : Nat := maskApply nCols m

@[expose] def xs8 (c : Nat) (f : Nat → Fin 8) : Fin 8 :=
  (if c.testBit 0 then f 0 else 0) ^^^ (if c.testBit 1 then f 1 else 0) ^^^
    (if c.testBit 2 then f 2 else 0) ^^^ (if c.testBit 3 then f 3 else 0) ^^^
    (if c.testBit 4 then f 4 else 0) ^^^ (if c.testBit 5 then f 5 else 0) ^^^
    (if c.testBit 6 then f 6 else 0) ^^^ (if c.testBit 7 then f 7 else 0)

@[expose] def nBetaTab : List (List (Fin 8)) := [[0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0, 0], [1, 7, 0, 0, 0, 0, 0, 0],
  [3, 6, 7, 0, 0, 0, 0, 0], [7, 2, 1, 5, 0, 0, 0, 0], [6, 1, 2, 4, 5, 0, 0, 0],
  [0, 4, 5, 3, 1, 6, 0, 0]]

@[expose] def nBT (j i : Nat) : Fin 8 := (nBetaTab.getD j []).getD i 0

@[expose] def nBeta (m n : Nat) : Fin 8 := xs8 (nCo m) fun j => xs8 (nCo n) (nBT j)

@[expose] def nAd (r : Lin8) (m : Nat) : Nat := maskApply (adMat r) m

@[expose] def nGam (r : Lin8) (m n : Nat) : Fin 8 :=
  nBeta (nAd r m) (nAd r n) ^^^ linApply r (nBeta m n)

@[expose] def nQuad (r : Lin8) (m : Nat) : Fin 8 :=
  xs8 (nCo m) fun j => xs8 (nCo m) fun i => if i < j then nGam r (nB i) (nB j) else 0

@[expose] def nTwTab : List (List (Fin 8)) := [
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0],
  [4, 0, 0, 7, 6, 0, 0, 5], [5, 0, 0, 6, 7, 0, 0, 4], [6, 0, 0, 5, 4, 0, 0, 7],
  [7, 0, 0, 4, 5, 0, 0, 6], [0, 4, 5, 0, 0, 6, 7, 0], [0, 5, 4, 0, 0, 7, 6, 0],
  [0, 6, 7, 0, 0, 4, 5, 0], [0, 7, 6, 0, 0, 5, 4, 0], [1, 1, 7, 0, 0, 0, 0, 5],
  [0, 0, 0, 5, 1, 1, 7, 0], [5, 0, 0, 0, 0, 7, 1, 1], [0, 7, 1, 1, 5, 0, 0, 0],
  [1, 1, 6, 0, 0, 0, 0, 4], [0, 0, 0, 4, 1, 1, 6, 0], [4, 0, 0, 0, 0, 6, 1, 1],
  [0, 6, 1, 1, 4, 0, 0, 0], [1, 1, 5, 0, 0, 0, 0, 7], [0, 0, 0, 7, 1, 1, 5, 0],
  [0, 5, 1, 1, 7, 0, 0, 0], [7, 0, 0, 0, 0, 5, 1, 1], [1, 1, 4, 0, 0, 0, 0, 6],
  [0, 0, 0, 6, 1, 1, 4, 0], [0, 4, 1, 1, 6, 0, 0, 0], [6, 0, 0, 0, 0, 4, 1, 1],
  [4, 0, 0, 6, 7, 0, 0, 5], [5, 0, 0, 7, 6, 0, 0, 4], [6, 0, 0, 4, 5, 0, 0, 7],
  [7, 0, 0, 5, 4, 0, 0, 6], [0, 4, 5, 0, 0, 7, 6, 0], [0, 5, 4, 0, 0, 6, 7, 0],
  [0, 6, 7, 0, 0, 5, 4, 0], [0, 7, 6, 0, 0, 4, 5, 0], [1, 1, 6, 0, 0, 0, 0, 5],
  [0, 0, 0, 5, 1, 1, 6, 0], [5, 0, 0, 0, 0, 6, 1, 1], [0, 6, 1, 1, 5, 0, 0, 0],
  [1, 1, 7, 0, 0, 0, 0, 4], [0, 0, 0, 4, 1, 1, 7, 0], [4, 0, 0, 0, 0, 7, 1, 1],
  [0, 7, 1, 1, 4, 0, 0, 0], [1, 1, 4, 0, 0, 0, 0, 7], [0, 0, 0, 7, 1, 1, 4, 0],
  [0, 4, 1, 1, 7, 0, 0, 0], [7, 0, 0, 0, 0, 4, 1, 1], [1, 1, 5, 0, 0, 0, 0, 6],
  [0, 0, 0, 6, 1, 1, 5, 0], [0, 5, 1, 1, 6, 0, 0, 0], [6, 0, 0, 0, 0, 5, 1, 1],
  [0, 0, 0, 7, 6, 0, 0, 3], [3, 0, 0, 6, 7, 0, 0, 0], [6, 0, 0, 3, 0, 0, 0, 7],
  [7, 0, 0, 0, 3, 0, 0, 6], [2, 1, 7, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 7, 1, 2],
  [0, 0, 0, 3, 2, 1, 7, 0], [0, 7, 1, 2, 3, 0, 0, 0], [2, 1, 6, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 6, 1, 2], [0, 0, 0, 0, 2, 1, 6, 0], [0, 6, 1, 2, 0, 0, 0, 0],
  [0, 0, 3, 0, 0, 6, 7, 0], [0, 3, 0, 0, 0, 7, 6, 0], [0, 6, 7, 0, 0, 0, 3, 0],
  [0, 7, 6, 0, 0, 3, 0, 0], [1, 2, 3, 0, 0, 0, 0, 7], [0, 3, 2, 1, 7, 0, 0, 0],
  [0, 0, 0, 7, 1, 2, 3, 0], [7, 0, 0, 0, 0, 3, 2, 1], [1, 2, 0, 0, 0, 0, 0, 6],
  [0, 0, 2, 1, 6, 0, 0, 0], [0, 0, 0, 6, 1, 2, 0, 0], [6, 0, 0, 0, 0, 0, 2, 1],
  [0, 0, 0, 6, 7, 0, 0, 3], [3, 0, 0, 7, 6, 0, 0, 0], [6, 0, 0, 0, 3, 0, 0, 7],
  [7, 0, 0, 3, 0, 0, 0, 6], [2, 1, 6, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 6, 1, 2],
  [0, 0, 0, 3, 2, 1, 6, 0], [0, 6, 1, 2, 3, 0, 0, 0], [2, 1, 7, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 7, 1, 2], [0, 0, 0, 0, 2, 1, 7, 0], [0, 7, 1, 2, 0, 0, 0, 0],
  [0, 0, 3, 0, 0, 7, 6, 0], [0, 3, 0, 0, 0, 6, 7, 0], [0, 6, 7, 0, 0, 3, 0, 0],
  [0, 7, 6, 0, 0, 0, 3, 0], [1, 2, 0, 0, 0, 0, 0, 7], [0, 0, 2, 1, 7, 0, 0, 0],
  [0, 0, 0, 7, 1, 2, 0, 0], [7, 0, 0, 0, 0, 0, 2, 1], [1, 2, 3, 0, 0, 0, 0, 6],
  [0, 3, 2, 1, 6, 0, 0, 0], [0, 0, 0, 6, 1, 2, 3, 0], [6, 0, 0, 0, 0, 3, 2, 1],
  [0, 0, 0, 5, 4, 0, 0, 3], [3, 0, 0, 4, 5, 0, 0, 0], [4, 0, 0, 3, 0, 0, 0, 5],
  [5, 0, 0, 0, 3, 0, 0, 4], [2, 1, 5, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 5, 1, 2],
  [0, 5, 1, 2, 3, 0, 0, 0], [0, 0, 0, 3, 2, 1, 5, 0], [2, 1, 4, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 4, 1, 2], [0, 4, 1, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 1, 4, 0],
  [1, 2, 3, 0, 0, 0, 0, 5], [0, 3, 2, 1, 5, 0, 0, 0], [5, 0, 0, 0, 0, 3, 2, 1],
  [0, 0, 0, 5, 1, 2, 3, 0], [1, 2, 0, 0, 0, 0, 0, 4], [0, 0, 2, 1, 4, 0, 0, 0],
  [4, 0, 0, 0, 0, 0, 2, 1], [0, 0, 0, 4, 1, 2, 0, 0], [0, 0, 3, 0, 0, 4, 5, 0],
  [0, 3, 0, 0, 0, 5, 4, 0], [0, 4, 5, 0, 0, 0, 3, 0], [0, 5, 4, 0, 0, 3, 0, 0],
  [0, 0, 0, 4, 5, 0, 0, 3], [3, 0, 0, 5, 4, 0, 0, 0], [4, 0, 0, 0, 3, 0, 0, 5],
  [5, 0, 0, 3, 0, 0, 0, 4], [2, 1, 4, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 4, 1, 2],
  [0, 4, 1, 2, 3, 0, 0, 0], [0, 0, 0, 3, 2, 1, 4, 0], [2, 1, 5, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 5, 1, 2], [0, 5, 1, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 1, 5, 0],
  [1, 2, 0, 0, 0, 0, 0, 5], [0, 0, 2, 1, 5, 0, 0, 0], [5, 0, 0, 0, 0, 0, 2, 1],
  [0, 0, 0, 5, 1, 2, 0, 0], [1, 2, 3, 0, 0, 0, 0, 4], [0, 3, 2, 1, 4, 0, 0, 0],
  [4, 0, 0, 0, 0, 3, 2, 1], [0, 0, 0, 4, 1, 2, 3, 0], [0, 0, 3, 0, 0, 5, 4, 0],
  [0, 3, 0, 0, 0, 4, 5, 0], [0, 4, 5, 0, 0, 3, 0, 0], [0, 5, 4, 0, 0, 0, 3, 0]]

@[expose] def nTw (r : Lin8) (j : Nat) : Fin 8 := (nTwTab.getD (glList.idxOf r) []).getD j 0

@[expose] def nTau (r : Lin8) (m : Nat) : Fin 8 := xs8 (nCo m) (nTw r) ^^^ nQuad r m

@[expose] def nCode (k : Nat) : Lin8 :=
  (⟨k / 64 % 8, Nat.mod_lt _ (by decide)⟩, ⟨k / 8 % 8, Nat.mod_lt _ (by decide)⟩,
    ⟨k % 8, Nat.mod_lt _ (by decide)⟩)

@[expose] def nIdx (r : Lin8) : Nat := r.1.val * 64 + r.2.1.val * 8 + r.2.2.val

@[expose] def nCoArr : Array Nat := Array.ofFn (n := 256) fun m => nCo m.val

@[expose] def nRowArr : Array (Fin 8) :=
  Array.ofFn (n := 2048) fun k => xs8 nCoArr[k.val % 256]! (nBT (k.val / 256))

@[expose] def nBetaF (m n : Nat) : Fin 8 := xs8 nCoArr[m]! fun j => nRowArr[256 * j + n]!

@[expose] def nBetaArr : Array (Fin 8) :=
  Array.ofFn (n := 65536) fun i => nBetaF (i.val / 256) (i.val % 256)

@[expose] def nAdArr (r : Lin8) : Array Nat :=
  let cols := adMat r
  Array.ofFn (n := 256) fun i => maskApply cols i.val

@[expose] def nGamBArr (r : Lin8) (ad : Array Nat) : Array (Fin 8) :=
  Array.ofFn (n := 64) fun k =>
    nBetaArr[ad[nB (k.val / 8)]! * 256 + ad[nB (k.val % 8)]!]! ^^^
      linApply r nBetaArr[nB (k.val / 8) * 256 + nB (k.val % 8)]!

@[expose] def nTauArrW (r : Lin8) (g : Array (Fin 8)) : Array (Fin 8) :=
  Array.ofFn (n := 256) fun m =>
    xs8 nCoArr[m.val]! (nTw r) ^^^
      xs8 nCoArr[m.val]! fun j => xs8 nCoArr[m.val]! fun i => if i < j then g[8 * i + j]! else 0

@[expose] def nAdTab : Array (Array Nat) :=
  Array.ofFn (n := 512) fun k =>
    let r := nCode k.val
    if indep3 r.1 r.2.1 r.2.2 then nAdArr r else #[]

@[expose] def nTauTab : Array (Array (Fin 8)) :=
  Array.ofFn (n := 512) fun k =>
    let r := nCode k.val
    if indep3 r.1 r.2.1 r.2.2 then nTauArrW r (nGamBArr r nAdTab[k.val]!) else #[]

@[expose] def nQuadCheck : Bool :=
  glList.all fun r =>
    let ad := nAdTab[nIdx r]!
    let tau := nTauTab[nIdx r]!
    (List.range 256).all fun m => (List.range 8).all fun j =>
      let b := nB j
      tau[m ^^^ b]! == tau[m]! ^^^ tau[b]! ^^^
        (nBetaArr[ad[m]! * 256 + ad[b]!]! ^^^ linApply r nBetaArr[m * 256 + b]!)

@[expose] def nCompCheck : Bool :=
  glList.all fun r => glList.all fun s =>
    let rs := linComp r s
    let adr := nAdTab[nIdx r]!
    let ads := nAdTab[nIdx s]!
    let adrs := nAdTab[nIdx rs]!
    let taur := nTauTab[nIdx r]!
    let taus := nTauTab[nIdx s]!
    let taurs := nTauTab[nIdx rs]!
    (List.range 8).all fun k =>
      adrs[2 ^ k]! == adr[ads[2 ^ k]!]! &&
        taurs[nB k]! == taur[ads[nB k]!]! ^^^ linApply r taus[nB k]!

@[expose] def nIdCheck : Bool :=
  (List.range 256).all (fun m => (nAdTab[nIdx linId]!)[m]! == m &&
    (nTauTab[nIdx linId]!)[m]! == 0 && maskApply nBasis nCoArr[m]! == m) &&
    glList.all (fun r => glList.contains (linInv r) && linComp (linInv r) r == linId &&
      linComp r (linInv r) == linId) &&
    glList.all (fun r => glList.all fun s => glList.contains (linComp r s))

@[expose] def nFaithCheck : Bool :=
  ((List.range 255).all fun m => (List.range 256).any fun n =>
    nBetaArr[(m + 1) * 256 + n]! != nBetaArr[n * 256 + (m + 1)]!) &&
    ((List.finRange 8).all fun t => (List.finRange 8).all fun t' =>
      t == 0 || t' == 0 || glList.any fun s => linApply s t == t')

abbrev NTrip : Type := Nat × Fin 8 × Lin8

@[expose] def nOneT : NTrip := (0, 0, linId)

@[expose] def nMulT (p q : NTrip) : NTrip :=
  let am := (nAdTab[nIdx p.2.2]!)[q.1]!
  (p.1 ^^^ am, p.2.1 ^^^ (linApply p.2.2 q.2.1 ^^^ (nTauTab[nIdx p.2.2]!)[q.1]!) ^^^
    nBetaArr[p.1 * 256 + am]!, linComp p.2.2 q.2.2)

@[expose] def nValid (p : NTrip) : Bool := decide (p.1 < 256) && glList.contains p.2.2

@[expose] def nImg : List NTrip := [
  (253, 4, (3, 6, 4)), (12, 0, (3, 2, 4)), (213, 4, (1, 6, 4)), (100, 5, (7, 2, 4)),
  (23, 3, (6, 5, 4)), (0, 0, (1, 2, 4)), (200, 3, (7, 2, 6))]

@[expose] def nImgInv : List NTrip := [
  (29, 2, (7, 6, 4)), (12, 0, (3, 2, 4)), (229, 1, (1, 6, 4)), (100, 5, (7, 2, 4)),
  (169, 2, (6, 5, 4)), (0, 0, (1, 2, 4)), (192, 1, (5, 2, 6))]

@[expose] def nRWords : List (List Nat) := [
  [0, 4, 12, 0, 6, 4, 12], [0, 6, 5, 0, 6, 4], [0, 0, 9, 5, 8], [0, 5, 9, 9, 4, 6, 5],
  [0, 0, 9, 9, 2, 6], [6, 0, 5, 8, 4, 8], [2, 5, 0, 6, 0, 4], [4, 6, 0, 4, 6, 0],
  [4, 4, 8, 4, 4, 9], [0, 4, 0, 4], [8, 8, 8, 8]]

@[expose] def nKWords : List (List Nat) := [
  [], [4, 0, 9, 13, 8, 1, 13], [0, 6, 2, 6, 1, 12], [0, 8, 1, 12, 8, 4, 6, 9],
  [0, 6, 1, 4, 8, 1], [4, 9, 0, 12, 0, 8, 5], [0, 8, 2, 8, 12, 9, 13], [0, 8, 5, 13, 9, 4, 8],
  [4, 6, 9, 9, 13, 0], [0, 8, 5, 2, 4, 13, 1], [13, 6, 8, 6, 2, 8], [9, 1, 9, 12, 0],
  [0, 12, 5, 2, 4, 9, 1], [12, 9, 1, 8, 5, 0, 12], [4, 0, 12, 6, 4, 8, 0], [12, 8, 13, 4, 8],
  [9, 2, 6, 9, 6, 12], [9, 5, 12, 9, 13], [2, 8, 0, 2, 9, 2], [4, 8, 5, 13, 1, 6, 8],
  [1, 13, 8, 0, 8], [4, 9, 5, 9, 2, 9, 12], [0, 8, 2, 8, 4, 8], [12, 5, 13, 1, 9, 4, 12],
  [0, 0, 8, 6, 4, 1], [8, 0, 13, 6, 0, 4], [8, 12, 9, 13, 4, 13], [4, 0, 8, 12, 9, 2, 4],
  [9, 5, 8, 1, 9, 5], [12, 0, 9, 1, 5, 12], [4, 4, 6, 12, 6, 5, 9], [0, 9, 5, 0, 0, 13],
  [9, 5, 6, 4, 13, 0], [2, 8, 0, 5, 13, 0], [0, 2, 4, 9, 12, 4, 6], [2, 4, 4, 8, 5, 12, 0],
  [6, 8, 2, 8, 0, 13], [4, 0, 5, 13, 8, 13, 8], [6, 1, 9], [4, 0, 13, 5, 9], [9, 12, 4, 8, 1, 5],
  [6, 9, 4, 13, 8, 2, 9], [0, 0, 9, 12, 9, 0, 5], [12, 9, 6, 13, 6, 0], [4, 12, 8, 0, 12, 6, 8],
  [0, 2, 4, 8, 1, 8, 12], [6, 5, 8, 6, 5, 2], [12, 6, 4, 1, 4, 9], [4, 8, 0, 9, 4, 8],
  [0, 5, 9, 5, 2, 9, 13], [0, 0, 13, 4, 8, 1], [13, 4, 0, 8, 1, 13], [1, 6, 0],
  [4, 8, 0, 12, 4, 9, 1], [0, 6, 0, 13], [0, 8, 5, 13, 1, 9, 5], [9, 0, 0, 12, 6, 5, 2],
  [0, 13, 6, 8, 8, 6, 1], [0, 4, 1, 9, 6, 13, 4], [0, 4, 12, 4, 8, 4, 9], [0, 4, 0, 8, 13, 0, 5],
  [1, 6, 13, 8, 0, 8], [4, 8, 6, 0, 6, 5], [6, 8, 13, 8, 2, 6], [9, 12, 1, 5, 2, 8, 0],
  [0, 12, 8, 0, 5, 0, 8], [0, 2, 8, 1, 9, 0, 8], [0, 5, 9, 5, 12, 4, 8], [12, 8, 0, 2, 4, 4, 12],
  [0, 6, 13, 1, 8, 0, 8], [2, 9, 12, 4, 9, 12, 8], [8, 4, 8, 13, 8, 2], [1, 12, 5, 6, 4, 8],
  [4, 0, 9, 5, 13, 8], [12, 1, 9, 2, 9, 6], [2, 5, 1, 12, 9, 13, 6], [4, 0, 2, 9, 0, 13, 9],
  [0, 8, 12, 8, 0, 6, 4], [0, 12, 0, 8, 4, 13, 5], [0, 9, 0, 12, 8, 6, 1], [8, 13, 5, 2, 0, 8],
  [4, 13, 1, 5, 8], [4, 4, 12, 5, 6, 9, 13], [13, 9, 2, 0, 5], [0, 0, 4, 12, 4, 4, 8],
  [8, 0, 4, 8, 12, 6, 8], [0, 12, 5, 12, 1, 9, 5], [1, 9, 2, 4, 0, 13, 8], [9, 2, 0, 4, 12, 9],
  [12, 8, 6, 8, 13, 0], [2, 0, 5, 8, 4, 12, 8], [12, 9, 6, 13, 0], [0, 0, 4, 12, 4, 12, 9, 13],
  [4, 13, 8, 4, 0, 5, 0], [9, 4, 12, 0, 5, 9], [12, 8, 5, 0, 6, 4], [1, 12, 4, 1, 9, 2],
  [8, 2, 9, 12, 5, 8, 6], [6, 13, 4, 9, 1, 9, 4], [8, 4, 13, 9, 0, 13, 9],
  [0, 6, 9, 12, 8, 2, 6], [8, 0, 8, 12, 1, 8, 1], [0, 4, 4, 6, 4, 6, 2], [6, 13, 6, 0, 4],
  [4, 8, 4, 0, 12, 5, 9], [1, 12, 4, 2, 9, 2], [6, 0, 4, 9, 2, 9], [2, 6, 5, 0, 8, 0, 13],
  [0, 6, 9, 9, 6, 12, 1], [2, 8, 0, 6, 5, 12, 5], [2, 6, 9, 4, 9, 13, 5], [9, 1, 9, 12, 6, 0],
  [8, 4, 1, 13, 5, 8], [4, 12, 5, 8, 8, 1], [6, 1, 9, 6, 1, 9], [0, 9, 0, 13, 9, 6],
  [2, 6, 9, 9, 13, 9, 12], [5, 9, 1, 8, 13, 6], [4, 6, 4, 8, 1, 4], [2, 6, 13, 8, 4, 0],
  [0, 12, 9, 4, 6, 0, 5], [1, 6, 12, 6, 8, 13], [8, 0, 6], [8, 5, 0, 5, 6, 13],
  [4, 0, 12, 4, 8, 12, 8], [0, 5, 9, 12, 0, 8, 0], [0, 9, 0, 12, 8, 0, 13],
  [0, 9, 0, 13, 9, 1, 9], [1, 12, 6, 8, 13], [2, 4, 0, 12, 5, 12, 8], [0, 6, 9, 2, 9, 6],
  [4, 8, 4, 1, 8, 12], [9, 4, 0, 12, 5], [9, 2, 4, 9, 13, 0], [2, 9, 1, 4, 8, 13, 0],
  [2, 8, 2, 5, 13, 0], [0, 12, 9, 12, 9, 0], [0, 12, 1, 5, 6, 0, 8], [0, 8, 1, 4, 9, 2],
  [6, 8, 12, 1, 8, 1], [0, 0, 5, 12, 1, 6, 8], [2, 9, 12, 9, 5, 9], [2, 5, 9, 0, 2, 4],
  [2, 6, 1, 13, 8, 1, 12], [0, 12, 1, 4, 0, 9, 2], [4, 0, 13, 8, 13, 8, 2], [2, 4, 6, 9, 4, 6],
  [8, 4, 12, 1, 5], [0, 6, 9, 13, 1, 8, 1], [0, 4, 0, 8, 12, 8, 12], [0, 4, 2, 6, 4, 4],
  [5, 1, 6, 12, 6], [1, 12, 9, 6, 9, 13], [1, 12, 8, 5, 2, 8], [9, 6, 2, 5, 13, 8, 2],
  [6, 12, 9, 0, 8, 4], [4, 0, 5, 0, 9, 12, 5], [4, 1, 4, 13, 8, 8, 4], [6, 4, 8, 1, 9, 13, 5],
  [0, 9, 9, 4, 13, 5], [4, 2, 0, 8, 12], [2, 9, 12, 4, 2, 6, 8], [4, 2, 4, 8, 6, 8],
  [4, 0, 12, 1, 9, 6, 5], [2, 8, 0, 5, 6, 8, 13], [2, 5, 9, 6, 12, 0, 9], [0, 8, 4, 9, 0, 6, 5],
  [6, 2, 9, 12, 9, 6]]

@[expose] def nSign (p : Fin 7 × Bool) : NTrip :=
  if p.2 then nImg.getD p.1 nOneT else nImgInv.getD p.1 nOneT

@[expose] def nEvalW (w : List (Fin 7 × Bool)) : NTrip :=
  w.foldl (fun x p => nMulT x (nSign p)) nOneT

@[expose] def nRTargets : List NTrip := [(16, 0, linId), (48, 0, linId), (117, 0, linId),
  (222, 0, linId), (210, 0, linId), (243, 0, linId), (188, 0, linId), (20, 0, linId),
  (0, 1, linId), (0, 2, linId), (0, 4, linId)]

@[expose] def nImgCheck : Bool :=
  (List.range 7).all fun i => nValid (nImg.getD i nOneT) && nValid (nImgInv.getD i nOneT) &&
    nMulT (nImg.getD i nOneT) (nImgInv.getD i nOneT) == nOneT

@[expose] def nRelCheck : Bool := relsA.all fun r => nEvalW (wordOfCodes 7 r) == nOneT

@[expose] def nCloCheck : Bool :=
  ((List.range 11).all fun i =>
    nEvalW (wordOfCodes 7 (nRWords.getD i [])) == nRTargets.getD i nOneT) &&
    ((List.range 168).all fun i =>
      nEvalW (wordOfCodes 7 (nKWords.getD i [])) == (0, 0, glList.getD i linId))

@[expose] def nA0Check : Bool :=
  ruA0Words.all fun w => (nEvalW w).1 == 0 && (nEvalW w).2.2 == linId

end CFSG.GMS78RuN
