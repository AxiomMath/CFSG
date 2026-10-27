module

public import CFSG.Sporadic.FischerOddCore.Fi24WitCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi24WitCheck
public import Certificates.Certificate2078Base
public meta import Certificates.Certificate2078Base
public import Certificates.Kernel.Sporadic.Fi24OrbL.Facts
public meta import Certificates.Kernel.Sporadic.Fi24OrbL.Facts

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native

@[expose] def fo24Packed (O : Enum) : Table :=
  Array.ofFn (n := nPts) fun i => O.par[i.1]! ||| (O.lab[i.1]! <<< 30)

@[expose] def fo24Gens (O : Enum) (l : Nat) : Table := if l = 1 then O.alpha else O.beta

@[expose] def fo24GensInv (O : Enum) (bInv : Table) (l : Nat) : Table :=
  if l = 1 then O.alpha else bInv

@[expose] def fo24ClsAt (O : Enum) (bInv pl tP : Table) (k : Nat) (q : Array Nat) : Array Nat :=
  applyTree pl (fo24Gens O) k (apT tP (applyTreeInv pl (fo24GensInv O bInv) k q))

@[noinline, expose] def fo24RowOK (R : Table) (q : Array Nat) : Bool :=
  allIn 0 nPts (fun x => ap R x == q[x]!)

@[noinline, expose] def fo24ProdOK (R : Table) (c1 c2 c3 : Array Nat) : Bool :=
  allIn 0 nPts (fun x => ap R x == c1[c2[c3[x]!]!]!)

@[noinline, expose] def fo24CommOK (O : Enum) (bInv pl tP : Table) (F u : Array Nat) : Bool :=
  allIn 0 F.size (fun j =>
    (fo24ClsAt O bInv pl tP F[j]! F == F) == (F[j]! == u[0]! || F[j]! == u[1]! || F[j]! == u[2]!))

@[noinline, expose] def fo24TripleAt (O : Enum) (bInv pl tP R : Table) (F u : Array Nat) : Bool :=
  F.size == 696 && u.size == 3 &&
    allIn 0 3 (fun i => decide (u[i]! < nPts) && ap R u[i]! == u[i]!) &&
    fo24CommOK O bInv pl tP F u &&
    fo24ProdOK R (fo24ClsAt O bInv pl tP u[0]! (Array.range nPts))
      (fo24ClsAt O bInv pl tP u[1]! (Array.range nPts))
      (fo24ClsAt O bInv pl tP u[2]! (Array.range nPts))

@[noinline, expose] def fo24TripleOK (O : Enum) (bInv pl tP R : Table) (u : Array Nat) : Bool :=
  fo24TripleAt O bInv pl tP R ((Array.range nPts).filter fun i => ap R i == i) u

@[noinline, expose] def fo24Checks (O : Enum) (k₀ : Nat) (u₂ u₃ : Array Nat) : Bool :=
  let L := chainLetters O
  let tA := wordT nPts (letterJ L) normWords[0]!
  let tB := wordT nPts (letterJ L) normWords[1]!
  let tP := tPTable O tA tB
  let M0 := wordT nPts (letterJ L) localWords[0]!
  let M1 := wordT nPts (letterJ L) localWords[1]!
  let gT := fi24GenT M0 (invT nPts M0) M1 (invT nPts M1)
  let D := powT nPts 7 (wordT nPts gT CFSG.Sporadic.Fi23.Native.dLetters)
  let W := wordT nPts gT fi23WordW
  let U2 := compT nPts D (compT nPts M0 (compT nPts D (invT nPts M0)))
  let U3 := compT nPts U2 (compT nPts W (compT nPts D (invT nPts W)))
  let pl := fo24Packed O
  let bInv := invT nPts O.beta
  tPOK O tA tB tP &&
    allIn 0 nPts (fun i => treePar (ap pl i) == ap O.par i && treeLab (ap pl i) == ap O.lab i) &&
    decide (k₀ < nPts) &&
    fo24RowOK (compT nPts D tP) (fo24ClsAt O bInv pl tP k₀ (Array.range nPts)) &&
    fo24TripleOK O bInv pl tP (compT nPts U2 tP) u₂ &&
    fo24TripleOK O bInv pl tP (compT nPts U3 tP) u₃

end CFSG.Sporadic.FischerOddCore
