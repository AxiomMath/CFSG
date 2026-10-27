module

public import Certificates.Data.Kernel.OpsV4
public import Certificates.Data.TripleCoverLift.Co3
public import Certificates.Data.TripleCoverLift.Co2
public import Certificates.Data.TripleCoverLift.Th
public import Certificates.Kernel.AlphaMc.SeedsF2
public import Certificates.Kernel.LocalComp.ThOrder
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCensus.LiftF2

open CFSG.KC.OpsV4 CFSG.KC.OpsK CFSG.RankThree.PartTwo.Sec4.Census CFSG.SectionRank.Native

theorem co3_K : liftN (opsF2K 22) KernelAM.C3A.M KernelAM.C3B.M co3Lift = true := by quickRfl

theorem co2_K : liftN (opsF2K 22) KernelAM.C2A.M KernelAM.C2B.M co2Lift = true := by quickRfl

theorem th_K : liftN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thLift = true := by quickRfl

theorem co3_neg_rep : liftN (opsF2K 22) KernelAM.C3A.M KernelAM.C3B.M
    { co3Lift with base := { co3Lift.base with outs := [39, 39, 51] } } = false := by
  decide +kernel

theorem co3_neg_inv : liftN (opsF2K 22) KernelAM.C3A.M KernelAM.C3B.M
    { co3Lift with inv₁ := 39 } = false := by decide +kernel

theorem co3_neg_rel : liftN (opsF2K 22) KernelAM.C3A.M KernelAM.C3B.M
    { co3Lift with rels := [.fix 65 0] } = false := by decide +kernel

theorem co3_neg_unit : liftN (opsF2K 22) KernelAM.C3A.M KernelAM.C3B.M
    { co3Lift with units := [(65, 1), (75, 12), (10, 4)] } = false := by decide +kernel

end CertificateChecks.KernelCensus.LiftF2

end
