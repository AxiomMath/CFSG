module

public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Co3Pump
meta import Certificates.Data.Co3Pump
meta import Certificates.Kernel.LocalComp.BfsGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelCo3Pair.E

public meta def aGL : List (Array Nat) :=
  (CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump.pairGensA ()).toList

meta def keyOf (a : Array Nat) : Nat := [0, 1, 2, 3, 4, 5, 6].foldr (fun p acc => a[p]! + 276 * acc) 0

meta def keyOrderA : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 276 9 aGL.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

end CertificateChecks.KernelCo3Pair.E

public section

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelCo3Pair.EA CertificateChecks.KernelCo3Pair.E.aGL 276 9 405
#kss_natlist CertificateChecks.KernelCo3Pair.EA.SKT CertificateChecks.KernelCo3Pair.E.keyOrderA

end
