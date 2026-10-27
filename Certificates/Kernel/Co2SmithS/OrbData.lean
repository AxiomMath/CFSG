module

public import CFSG.Sporadic.Co2Smith.CheckInputs
public meta import CFSG.Sporadic.Co2Smith.CheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
public meta import Certificates.Data.CFSGNative.Co2Smith.Check
public import Certificates.Data.CFSGNative.Co2Smith.Check
import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

namespace CertificateChecks.KernelCo2SmithS

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Smith.Native

meta def recOf (step : Nat → Nat → Nat) (ngen : Nat) (r : Array Nat × Array Nat × Array Nat) :
    Array Nat × Array (Array Nat) := Id.run do
  let pts := r.1
  let par := r.2.1
  let n := pts.size
  let pm := posMapN pts
  let mut cnt : Array Nat := Array.replicate (n + 1) 0
  for i in [1:n] do
    cnt := cnt.set! par[i]! (cnt[par[i]!]! + 1)
  let mut m : Array Nat := #[1]
  let mut c := 1
  for h in [0:n] do
    c := c + cnt[h]!
    m := m.push c
  let s := (List.range n).toArray.qsort fun i j => pts[i]! < pts[j]!
  let tb := (List.range ngen).toArray.map fun l => pts.map fun x => pm.getD (step l x) n
  return (pts, #[par, r.2.2, m, s] ++ tb)

meta def pairRec : Array Nat × Array (Array Nat) :=
  let G := #[mRows seedRowsArr [2], mRows seedRowsArr [3]]
  let start := pairU * 4194304 + pairV
  recOf (pairStep G) 2 (orbitBFS (pairStep G) 2 start 20000)

meta def chainRec (k : Nat) : Array Nat × Array (Array Nat) :=
  let G := (chainGens ())[k]!.map (mRows seedRowsArr)
  recOf (vecStep G) G.size (orbitBFS (vecStep G) G.size chainBase[k]! 100)

meta def orbRecs : Array (Array Nat × Array (Array Nat)) :=
  #[pairRec] ++ (List.range 6).toArray.map chainRec

meta def orbPts : Array (Array Nat) := orbRecs.map (·.1)

meta def orbIdx : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := #[]
  for r in orbRecs do
    out := out ++ r.2 ++ Array.replicate (16 - r.2.size) #[]
  return out

end CertificateChecks.KernelCo2SmithS

#kc_items CertificateChecks.KernelCo2SmithS.OPT include_bytes "data/OrbData.OPT.items" 42271 17518987327305928721
#kc_items CertificateChecks.KernelCo2SmithS.OPI include_bytes "data/OrbData.OPI.items" 93248 16516263348938615883
