module

public import CFSG.Certificates.Kernel.BabyMonster.FiveAFacts
public import CFSG.Certificates.Kernel.BabyMonster.RegRun
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data19
public import Certificates.Data.CFSGNative.MonsterB.Primes
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.FiveA.Facts13610
import Certificates.Kernel.BabyMonster.Five.Regs
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

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.BM CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Primes.Native in
theorem certificate13612 : decode 2 4370 1 BSeed1 = stripMat Seeds.A1 ∧ decode 2 4370 1 BSeed2 = stripMat Seeds.A2 ∧
    Reg.RegsOK fiveProg [(1, some Seeds.A1), (2, some Seeds.A2)] true [1, 2] [Five.f85, Five.f86] ∧
    FiveA.Fact13612 (stripMat Five.f85) (stripMat Five.f86) :=
  ⟨KernelBM.genA₁_eq_stripMat, KernelBM.genA₂_eq_stripMat, KernelBM.Five.five_regs,
    KernelBM.FiveA.fact13612⟩

end Certificates
