module

public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Co3Pump
meta import Certificates.Data.Co3Pump
meta import Certificates.Kernel.LocalComp.BfsGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelCo3Pair.E

public meta def bGL : List (Array Nat) :=
  (CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump.pairGensB ()).toList

meta def keyOfB (a : Array Nat) : Nat := [0, 1, 2, 3, 4, 5, 6].foldr (fun p acc => a[p]! + 276 * acc) 0

meta def keyOrderB : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 276 9 bGL.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOfB pts[a]! < keyOfB pts[b]!).toList

end CertificateChecks.KernelCo3Pair.E

public section

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelCo3Pair.EB CertificateChecks.KernelCo3Pair.E.bGL 276 9 540
#kss_natlist CertificateChecks.KernelCo3Pair.EB.SKT CertificateChecks.KernelCo3Pair.E.keyOrderB

end
