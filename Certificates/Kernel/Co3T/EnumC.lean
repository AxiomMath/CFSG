module

public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
meta import Certificates.Kernel.LocalComp.BfsGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelCo3T.E

public meta def cGL : List (Array Nat) :=
  (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.cGens ()).toList

meta def keyOf (a : Array Nat) : Nat := [0, 1, 2, 3, 4, 5, 6].foldr (fun p acc => a[p]! + 276 * acc) 0

meta def keyOrder : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 276 9 cGL.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

end CertificateChecks.KernelCo3T.E

public section

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelCo3T.EC CertificateChecks.KernelCo3T.E.cGL 276 9 504
#kss_natlist CertificateChecks.KernelCo3T.EC.SKT CertificateChecks.KernelCo3T.E.keyOrder

end
