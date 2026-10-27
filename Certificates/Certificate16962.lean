module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElementsParts
import Certificates.Kernel.BabyMonster.B7EParts
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

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate16962 : B7EParts a0B7 xB7 yB7 t1B7 t2B7 eB7 :=
  KernelBM.B7EParts.b7EParts

end Certificates
