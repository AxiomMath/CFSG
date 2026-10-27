
module

public import CFSG.Sporadic.ThSchreier.TransporterBase
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

@[expose] def rowsT : Array V4 := mulRows (mulRows rowsVInv rowsA) rowsV

@[expose] def conjRowsH (l : ℕ) (E : Array V4) : Array V4 :=
  if l = 1 then mulRows (mulRows rowsLX E) rowsLX
  else mulRows (mulRows rowsLY E) (mulRows rowsLY rowsLY)

@[expose] def orbPar (i : ℕ) : ℕ := centOrbitPar.getD i 0

@[expose] def orbLab (i : ℕ) : ℕ := centOrbitLab.getD i 0

@[expose] def orbEdge (i s : ℕ) : ℕ := centOrbitEdges.getD (2 * i + (s - 1)) 0

@[expose] def orbRows (i : ℕ) : Array V4 :=
  if _h : 0 < i ∧ orbPar i < i then conjRowsH (orbLab i) (orbRows (orbPar i)) else rowsT
@[expose] def orbTable : Array (Array V4) := Array.ofFn (n := 819) fun i => orbRows i

@[noinline, expose] def orbitChecks (E : Array (Array V4)) : Bool :=
  E.size == 819 &&
  (List.range 819).all (fun i => (i == 0 || (orbPar i < i && (orbLab i == 1 || orbLab i == 2))) &&
    orbEdge i 1 < 819 && orbEdge i 2 < 819 &&
    eqRows (conjRowsH 1 E[i]!) E[orbEdge i 1]! && eqRows (conjRowsH 2 E[i]!) E[orbEdge i 2]!) &&
  (List.range 819).all (fun i => (List.range i).all fun j => !eqRows E[i]! E[j]!)

end CFSG.Sporadic.ThSchreier
