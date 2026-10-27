module

public import CFSG.RankThree.Native.Co3FiveCheckInputs
public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.RankThree.Native.Co3FiveCheckInputs
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo3Five

open CFSG.RankThree.Native CFSG.KC.BfsGen CFSG.KS.RawGen

meta def c25L : List (Array Nat) := co3FiveC25GenArrs.toList

meta def qL : List (Array Nat) := co3FiveQGenArrs.toList

meta def c0L : List (Array Nat) := co3FiveC0GenArrs.toList

meta def dL : List (Array Nat) := co3FiveDGenArrs.toList

meta def keyOf (a : Array Nat) : Nat := co3FiveKeyPts.foldr (fun p acc => a[p]! + 276 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (search 276 9 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def k25 : List Nat := keyOrder c25L

meta def kq : List Nat := keyOrder qL

meta def k0 : List Nat := keyOrder c0L

meta def kd : List Nat := keyOrder dL

meta def powM (x : Array Nat) (e : Nat) : Array Nat :=
  (List.range e).foldl (fun acc _ => comp 276 x acc) (Array.range 276)

meta def lines : Array (Array Nat) := co3FiveLines

meta def zM : Array (Array Nat) := #[co3FiveZArr]

meta def dM : Array (Array Nat) := co3FiveDGenArrs

meta def wq : List Nat :=
  let pts := (search 276 9 co3FiveQGenArrs).1
  pts.toList.map fun x => Id.run do
    for j in [0:31] do
      for e in [0:5] do
        if x == powM lines[j]! e then return 5 * j + e
    return 0

meta def wt : Array (Array Nat) :=
  let as := (search 276 9 co3FiveDGenArrs).1
  let N := as.size
  let idx : Std.HashMap Nat Nat := (Array.range N).foldl (fun m i => m.insert (pack 9 as[i]!) i) {}
  as.map fun ak => Id.run do
    let mut rs : Array Nat := Array.replicate N 0
    if ak == Array.range 276 then return rs
    let cs := as.map fun aj => comp 276 aj (comp 276 ak (inv 276 aj))
    let mut seen : Array Bool := (Array.replicate N false).set! 0 true
    let mut q : Array Nat := #[0]
    let mut h := 0
    while h < q.size do
      let p := q[h]!
      for j in [0:N] do
        let y := comp 276 cs[j]! as[p]!
        let i := idx.getD (pack 9 y) 0
        if !seen[i]! then
          seen := seen.set! i true
          rs := rs.set! i (j + 64 * p + 4096 * (rs[p]! / 4096 + 1))
          q := q.push i
      h := h + 1
    return rs

end CertificateChecks.KernelCo3Five

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCo3Five.FC CFSG.RankThree.Native.co3FiveHex
#kmisc_hexflat CertificateChecks.KernelCo3Five.FC CFSG.RankThree.Native.co3FiveHex 3 276 9 40

#lc_bfs CertificateChecks.KernelCo3Five.S25 CertificateChecks.KernelCo3Five.c25L 276 9
#lc_bfs CertificateChecks.KernelCo3Five.SQ CertificateChecks.KernelCo3Five.qL 276 9
#lc_bfs CertificateChecks.KernelCo3Five.S0 CertificateChecks.KernelCo3Five.c0L 276 9
#lc_bfs CertificateChecks.KernelCo3Five.SD CertificateChecks.KernelCo3Five.dL 276 9

#kss_natlist CertificateChecks.KernelCo3Five.K25 CertificateChecks.KernelCo3Five.k25
#kss_natlist CertificateChecks.KernelCo3Five.KQ CertificateChecks.KernelCo3Five.kq
#kss_natlist CertificateChecks.KernelCo3Five.K0 CertificateChecks.KernelCo3Five.k0
#kss_natlist CertificateChecks.KernelCo3Five.KD CertificateChecks.KernelCo3Five.kd

#kmisc_packarrs CertificateChecks.KernelCo3Five.LN CertificateChecks.KernelCo3Five.lines 9
#kmisc_packarrs CertificateChecks.KernelCo3Five.ZZ CertificateChecks.KernelCo3Five.zM 9
#kmisc_packarrs CertificateChecks.KernelCo3Five.DG CertificateChecks.KernelCo3Five.dM 9
#kss_natlist CertificateChecks.KernelCo3Five.WQ CertificateChecks.KernelCo3Five.wq
#kmisc_packarrs CertificateChecks.KernelCo3Five.WT CertificateChecks.KernelCo3Five.wt 16
