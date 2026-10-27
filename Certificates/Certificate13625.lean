module

public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Struct
public import CFSG.Monster.B.Pinned.Primes.FiveWords
public import Certificates.Certificate3109
import Certificates.Kernel.BabyMonster.FiveA.CoverB
public import CFSG.Certificates.Kernel.BabyMonster.Sound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Cbar.SimpleBase
public import CFSG.Monster.B.Max2.Pinned
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Pinned CFSG.KC.BM.PcFive in
theorem certificate13625 : FiveRel xFive hFive ∧ Fact13625 xFive hFive :=
  KernelBM.FiveA.fact13625_B

end Certificates
