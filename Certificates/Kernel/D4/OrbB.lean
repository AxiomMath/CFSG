module

public import Certificates.Kernel.D4.ChainBD
public import Certificates.Kernel.D4.EnumB
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Kernel.SporSch.Th.GenV4
meta import Certificates.Data.Item434D42

namespace CertificateChecks.KernelD4.OB

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

meta def orbL : List Nat × List Nat × List Nat := Id.run do
  let p := ((rawLevels 2457 d4ChainBArrs d4ChainBBaseArr)[0]!).pts
  let c := d4CBCert.pts
  let mut idx := Array.replicate 2457 0
  for k in [0:p.size] do
    idx := idx.set! (p[k]!) k
  let mut ri := Array.replicate p.size p.size
  let mut ek := Array.replicate p.size 0
  let mut reps : Array Nat := #[]
  for k in [0:p.size] do
    if ri[k]! == p.size then
      let j := reps.size
      reps := reps.push k
      let q := p[k]!
      for e in [0:c.size] do
        let t := idx.getD ((c.getD e #[]).getD q 0) 0
        if ri[t]! == p.size then
          ri := ri.set! t j
          ek := ek.set! t e
  return (reps.toList, ri.toList, ek.toList)

meta def repL : List Nat := orbL.1
meta def riL : List Nat := orbL.2.1
meta def ekL : List Nat := orbL.2.2

end CertificateChecks.KernelD4.OB

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelD4.RB CertificateChecks.KernelD4.OB.repL
#kss_natlist CertificateChecks.KernelD4.RIB CertificateChecks.KernelD4.OB.riL
#kss_natlist CertificateChecks.KernelD4.EKB CertificateChecks.KernelD4.OB.ekL

namespace CertificateChecks.KernelD4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail

@[expose] noncomputable def orbKB (k : Nat) : Bool :=
  Nat.blt (RIB k) 7 && Nat.blt (RB (RIB k)) 2457 && Nat.blt (EKB k) EB.N &&
    Nat.beq (pg 12 (mask 12) (EB.T (EKB k)) (rpt 12 (mask 12) (CB.LR 0) (RB (RIB k))))
      (rpt 12 (mask 12) (CB.LR 0) k)

end CertificateChecks.KernelD4

end
