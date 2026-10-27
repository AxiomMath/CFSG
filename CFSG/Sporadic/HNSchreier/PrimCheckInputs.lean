module

public import CFSG.Sporadic.HNSchreier.OrbitCheck
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import Certificates.Data.CFSGNative.Perm.Chain
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

@[expose] def progRegs (n : Nat) (regs : Array (Array Nat)) : List (Nat × Nat × Nat) →
    Array (Array Nat)
  | [] => regs
  | (a, b, c) :: rest => progRegs n (regs.set! c (pcomp n regs[a]! regs[b]!)) rest

@[expose] def initRegs (n : Nat) (a0 a1 : Array Nat) : Array (Array Nat) :=
  #[pid n, a0, a1] ++ Array.replicate 8 (pid n)

@[expose] def toTable (t : Array Nat) : Table := t.map UInt32.ofNat

@[expose] def subLabels (n : Nat) (Ts : Array Tree) : Array Nat := Id.run do
  let mut lab : Array Nat := Array.replicate n Ts.size
  for j in [0:Ts.size] do
    let T := Ts[j]!
    for t in [0:T.pts.size] do
      lab := lab.set! (ap T.pts t) j
  return lab

@[noinline, expose] def subChecksH (n : Nat) (h1 h2 : Table) : Bool :=
  let letters := #[h1, h2]
  let reps := Data.subgroupOrbitReps.toArray
  let Ts := reps.map fun r => treeBFS n r letters #[0, 1]
  let lab := subLabels n Ts
  ap h1 0 == 0 && ap h2 0 == 0 && h1.size == n && h2.size == n && reps.size == 12 &&
    (Ts.toList.map fun T => T.pts.size) == Data.subgroupOrbitSizes &&
    allIn 0 12 (fun j => decide (reps[j]! < n) && treeOK n reps[j]! Ts[j]! letters #[0, 1]) &&
    allIn 0 n (fun p => decide (lab[p]! < 12) && ap Ts[lab[p]!]!.pos p < Ts[lab[p]!]!.pts.size &&
      ap Ts[lab[p]!]!.pts (ap Ts[lab[p]!]!.pos p) == p) &&
    allIn 0 12 (fun j => allIn 0 12 fun k => j == k || !(ap Ts[j]!.pos reps[k]! <
      Ts[j]!.pts.size && ap Ts[j]!.pts (ap Ts[j]!.pos reps[k]!) == reps[k]!)) &&
    allIn 0 12 (fun j => allIn 0 Ts[j]!.pts.size fun t => decide (reps[j]! ≤ ap Ts[j]!.pts t)) &&
    divOK n Data.subgroupOrbitSizes

@[noinline, expose] def primChecks (O : VOrbit) : Bool :=
  let n := hnsData.n
  let regs := progRegs n (initRegs n (natTab O.alpha) (natTab O.beta)) Data.subgroupProgram
  regs.size == 11 && allIn 0 n (fun i => decide (regs[1]![i]! < n) && decide (regs[2]![i]! < n)) &&
    subChecksH n (toTable regs[1]!) (toTable regs[2]!)

@[expose] def ppow (n : Nat) (t : Array Nat) : Nat → Array Nat
  | 0 => pid n
  | e + 1 => pcomp n (ppow n t e) t

@[expose] def conjProdWord : List Int :=
  [1, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]

@[noinline, expose] def orderChecks (n : Nat) (a0 a1 : Array Nat) : Bool :=
  let S := #[a0, a1]
  let Si := pinvs n S
  let x := pword n S Si conjProdWord
  pisInv n a0 Si[0]! && pisInv n a1 Si[1]! && peq n (ppow n a0 2) (pid n) &&
    !(peq n a0 (pid n)) && peq n (ppow n a1 3) (pid n) && !(peq n a1 (pid n)) &&
    peq n (ppow n x 19) (pid n) && !(peq n x (pid n))

end CFSG.Sporadic.HNSchreier.Native
