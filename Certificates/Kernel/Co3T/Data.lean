module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
meta import Certificates.Kernel.LocalComp.BfsGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

namespace CertificateChecks.KernelCo3T.E

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu

meta def cmp (t u : Array Nat) : Array Nat := u.map fun i => t[i]!

meta def inv (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate t.size 0
  for i in [0:t.size] do
    r := r.set! t[i]! i
  return r

meta def one : Array Nat := Array.range 276

meta def pwr (t : Array Nat) : Nat → Array Nat
  | 0 => one
  | e + 1 => cmp t (pwr t e)

meta def lines : Array (Array Nat) := (Array.range 36).map perm

meta def ln (L : Nat) : Array Nat := lines[L]!

meta def lv : Array Level := levels ()

meta def dE : Array (Array Nat) := Id.run do
  let d := (Array.range 5).map fun i => ln (4 + i)
  let p := d.map fun x => #[one, x, cmp x x]
  return Array.ofFn (n := 243) fun k =>
    cmp (p[0]!)[k.val / 1 % 3]! (cmp (p[1]!)[k.val / 3 % 3]! (cmp (p[2]!)[k.val / 9 % 3]!
      (cmp (p[3]!)[k.val / 27 % 3]! (p[4]!)[k.val / 81 % 3]!)))

meta def gJ : Array (Array Nat) := hypTuples.map (rebuild lv)

meta def cK : List Nat := Id.run do
  let e := dE
  let g := gJ
  return (List.range 121).flatMap fun j => (List.range 7).map fun l =>
    ((List.range 243).find? fun k => (e[k]!)[(g[j]!)[0]!]! == (g[j]!)[l]!).getD 243

meta def dIdx : Std.HashMap (Array Nat) Nat := Id.run do
  let e := dE
  return (List.range 243).foldl (fun m k => if m.contains e[k]! then m else m.insert e[k]! k) {}

meta def qPts : Array (Array Nat) := (CFSG.KC.BfsGen.search 276 9 (qGens ())).1

meta def conjIdx : Std.HashMap (Array Nat) (Nat × Nat) := Id.run do
  let ys := (List.range 24).toArray.map fun j =>
    if j < 12 then ln (12 + j) else cmp (ln (12 + (j - 12))) (ln (12 + (j - 12)))
  let q := qPts
  let mut m : Std.HashMap (Array Nat) (Nat × Nat) := {}
  for u in [0:q.size] do
    let g := q[u]!
    let gi := inv g
    for j in [0:24] do
      let t := cmp gi (cmp ys[j]! g)
      if !m.contains t then
        m := m.insert t (u, j)
  return m

meta def fusL : List (Nat × Nat × Nat) := Id.run do
  let di := dIdx
  let ci := conjIdx
  return qPts.toList.map fun t =>
    if pwr t 3 != one || t == one then (0, 0, 0)
    else match di.get? t with
      | some k => (1, k, 0)
      | none => match ci.get? t with
        | some (u, j) => (2, u, j)
        | none => (0, 0, 0)

meta def fwL : List Nat := fusL.map (·.1)
meta def faL : List Nat := fusL.map (·.2.1)
meta def fbL : List Nat := fusL.map (·.2.2)

meta def tdL : List Nat := Id.run do
  let di := dIdx
  return (List.range 12).map fun j =>
    let h := ln (24 + j)
    (di.get? (cmp h (cmp (ln (12 + j)) (inv h)))).getD 0

meta def cPts : Array (Array Nat) := (CFSG.KC.BfsGen.search 276 9 (cGens ())).1

meta def movedBy (x : Array Nat) : Nat := ((List.range 276).find? fun p => x[p]! != p).getD 0

meta def clsL : List (Nat × Nat × Nat) := cPts.toList.map fun w =>
  let w2 := pwr w 2
  let w7 := pwr w 7
  (if w == one then 0 else if w2 == one || w7 == one then 1 else 0, movedBy w2, movedBy w7)

meta def cwL : List Nat := clsL.map (·.1)
meta def c2L : List Nat := clsL.map (·.2.1)
meta def c7L : List Nat := clsL.map (·.2.2)

end CertificateChecks.KernelCo3T.E

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelCo3T.DE include_bytes "data/Data.DE.items" 76516 6124159290139950512
#kc_items CertificateChecks.KernelCo3T.GJ include_bytes "data/Data.GJ.items" 38094 16392421479992167502
#kc_items CertificateChecks.KernelCo3T.CK include_bytes "data/Data.CK.items" 4114 4698415643742360208
#kc_items CertificateChecks.KernelCo3T.FW include_bytes "data/Data.FW.items" 9638 4324762310215120322
#kc_items CertificateChecks.KernelCo3T.FA include_bytes "data/Data.FA.items" 9614 3305349688864001639
#kc_items CertificateChecks.KernelCo3T.FB include_bytes "data/Data.FB.items" 9369 11171046779513882191
#kc_items CertificateChecks.KernelCo3T.TD include_bytes "data/Data.TD.items" 52 15518156833797331185
#kc_items CertificateChecks.KernelCo3T.CW include_bytes "data/Data.CW.items" 18423 17124989682294343136
#kc_items CertificateChecks.KernelCo3T.C2 include_bytes "data/Data.C2.items" 18188 4980104372293403561
#kc_items CertificateChecks.KernelCo3T.C7 include_bytes "data/Data.C7.items" 18170 18310916860489493959

end
