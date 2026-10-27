
module

public import CFSG.Monster.B.Fischer.InducedChecksBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.Fischer.InducedChecksBase
public meta import CFSG.Monster.B.TwoA.Census.NatCert

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.TwoA.Census

@[expose] def wCert (s : ℕ) : NatCert := natBfs linW 2 s 1100

@[expose] def indA : Array ℕ := indM22Gen 0

@[expose] def indB : Array ℕ := indM22Gen 1

@[expose] def indAB (g : ℕ) : Array ℕ := if g = 0 then indA else indB

@[expose] def zAct (g n : ℕ) : ℕ := (indAB g)[1046 + n]! - 1046

@[expose] def zCert (s : ℕ) : NatCert := natBfs zAct 2 s 2500

@[expose] def genArr (z : ℤ) : Array ℕ := if z = 1 then indA else indB

@[expose] def wordArr (w : List ℤ) : Array ℕ :=
  w.foldr (fun z acc => amulN (genArr z) acc) (idArrN 3510)

@[expose] def sWord (k : ℕ) : List ℤ :=
  [[2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2,
      2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2],
    [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1,
      2],
    [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2,
      1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1],
    [1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2,
      1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1]].getD k []

@[expose] def s2Word (k : ℕ) : List ℤ :=
  [[1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1],
    [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2,
      2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2],
    [2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2,
      2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2]].getD k []

@[expose] def sArrs : Array (Array ℕ) := ((List.range 4).map fun k => wordArr (sWord k)).toArray

@[expose] def s2Arrs : Array (Array ℕ) := ((List.range 3).map fun k => wordArr (s2Word k)).toArray

@[expose] def sigmaTable : Array ℕ :=
  indSigma.foldl (fun t p => t.set! p.1 p.2) (Array.replicate 1024 0)

@[expose] def tauTable : Array ℕ :=
  indTau.foldl (fun t p => t.set! p.1 p.2) (Array.replicate 2464 0)

@[expose] def sigmaFun (u : ℕ) : ℕ := sigmaTable[u]!

@[expose] def tauFun (n : ℕ) : ℕ := tauTable[n]!

@[expose] def hexMask (s : Finset (Fin 24)) : ℕ := ∑ c ∈ s, 2 ^ ((c : ℕ) - 2)

end CFSG.Monster.B.Fischer
