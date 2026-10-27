module

public import Certificates.Kernel.D4.Tabs
public import Certificates.Kernel.D4.ChainAD
public import Certificates.Kernel.D4.EnumA
public import Certificates.Data.Kernel.D4K
public import Certificates.Data.Kernel.Misc.ChainTailOrb
public import Certificates.Kernel.SporSch.Th.GenV4
meta import Certificates.Data.Item434D42
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelD4.OA

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne

meta def orbL : List Nat × List Nat × List Nat := Id.run do
  let p := ((rawLevels 2457 d4ChainAArrs d4ChainABaseArr)[0]!).pts
  let c := d4CACert.pts
  let xs := powPA 3 2457 d4Lines[0]!
  let mut idx := Array.replicate 2457 0
  for k in [0:p.size] do
    idx := idx.set! (p[k]!) k
  let mut ri := Array.replicate p.size p.size
  let mut ek := Array.replicate p.size 0
  let mut reps : Array Nat := #[]
  for k in [0:p.size] do
    if ri[k]! == p.size && relOK d4ChainABaseArr xs d4RelsA 0 (idA 2457) p[k]! then
      let j := reps.size
      reps := reps.push k
      let q := p[k]!
      for e in [0:c.size] do
        let t := idx.getD ((c.getD e #[]).getD q 0) 0
        if ri[t]! == p.size then
          ri := ri.set! t j
          ek := ek.set! t e
  return (reps.toList, (ri.map fun i => if i == p.size then 0 else i).toList, ek.toList)

meta def repL : List Nat := orbL.1
meta def riL : List Nat := orbL.2.1
meta def ekL : List Nat := orbL.2.2

end CertificateChecks.KernelD4.OA

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelD4.RA CertificateChecks.KernelD4.OA.repL
#kss_natlist CertificateChecks.KernelD4.RIA CertificateChecks.KernelD4.OA.riL
#kss_natlist CertificateChecks.KernelD4.EKA CertificateChecks.KernelD4.OA.ekL

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.D4K

theorem tbA0 : repBranchK 2457 12 CA.LR CA.TR CA.BP (LX 0) (pw 2457 12 (LX 0)) d4RelsA EA.N EA.T 7
    (RA 0) = true := by quickRfl

theorem kOrbA : allN 2457 (orbRelK 2457 12 CA.LR CA.BP (pw 2457 12 (LX 0)) d4RelsA EA.N EA.T 1 RA
    RIA EKA) = true := by quickRfl

end CertificateChecks.KernelD4

end
