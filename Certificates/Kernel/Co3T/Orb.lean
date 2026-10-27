module

public import Certificates.Kernel.Co3T.Defs
public import Certificates.Kernel.SporSch.Th.GenV4
meta import Certificates.Kernel.Co3T.EnumC
meta import Certificates.Kernel.LocalComp.BfsGen
meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs

namespace CertificateChecks.KernelCo3T.E

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

meta def lv0 : Array Nat := ((levels ())[0]!).pts

meta def findE (c : Array (Array Nat)) (src dst : Nat) : Nat :=
  ((List.range c.size).find? fun e => (c.getD e #[]).getD src 0 == dst).getD c.size

meta def orbL : List Nat × List Nat × List Nat := Id.run do
  let p := lv0
  let c := (CFSG.KC.BfsGen.search 276 9 cGL.toArray).1
  let in0 : Nat → Bool := fun k => decide (findE c (p.getD 0 0) (p.getD k 0) < c.size)
  let r1 := ((List.range p.size).find? fun k => !(in0 k)).getD 0
  let rk := (List.range p.size).map fun k => if in0 k then 0 else r1
  let ek := (List.range p.size).map fun k =>
    findE c (p.getD (if in0 k then 0 else r1) 0) (p.getD k 0)
  return ([0, r1], rk, ek)

meta def repL : List Nat := orbL.1
meta def rkL : List Nat := orbL.2.1
meta def ekL : List Nat := orbL.2.2

end CertificateChecks.KernelCo3T.E

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelCo3T.REP CertificateChecks.KernelCo3T.E.repL
#kss_natlist CertificateChecks.KernelCo3T.RK CertificateChecks.KernelCo3T.E.rkL
#kss_natlist CertificateChecks.KernelCo3T.EK CertificateChecks.KernelCo3T.E.ekL

namespace CertificateChecks.KernelCo3T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.KC.Co3TK CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
open CertificateChecks.KernelSpor

@[expose] noncomputable def orbK (k : Nat) : Bool :=
  Nat.blt (RK k) 276 && (Nat.beq (RK k) (REP 0) || Nat.beq (RK k) (REP 1)) &&
    Nat.blt (EK k) EC.N &&
    Nat.beq (pg 9 (mask 9) (EC.T (EK k)) (rpt 9 (mask 9) (Co3C.LR 0) (RK k)))
      (rpt 9 (mask 9) (Co3C.LR 0) k)

end CertificateChecks.KernelCo3T

end
