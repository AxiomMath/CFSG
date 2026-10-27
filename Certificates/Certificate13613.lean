module

public import CFSG.Certificates.Kernel.BabyMonster.FiveMFacts
public import CFSG.Certificates.Kernel.BabyMonster.RegRun
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data4
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAInputs
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.FiveA.Facts13613
import Certificates.Kernel.BabyMonster.Max15Run
import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Max2.Pinned
public import CFSG.Monster.B.Pinned.GeneratorDeterminants
public import CFSG.Open.Defs
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.BM CFSG.Blueprint.NativeSporadic
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native in
theorem certificate13613 : decode 2 4370 1 BSeed1 = stripMat Seeds.A1 ∧ decode 2 4370 1 BSeed2 = stripMat Seeds.A2 ∧
    Reg.RegsOK (max15Prog ()) [(1, some Seeds.A1), (2, some Seeds.A2)] true [1, 2]
      [Max15.g1, Max15.g2] ∧
    FiveM.Fact13613 (stripMat Max15.g1) (stripMat Max15.g2) :=
  ⟨KernelBM.genA₁_eq_stripMat, KernelBM.genA₂_eq_stripMat, KernelBM.Max15Run.max15_regs,
    KernelBM.FiveA.fact13613⟩

end Certificates
