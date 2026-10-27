module

public import CFSG.Certificates.Kernel.BabyMonster.HSFacts
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAInputs
import Certificates.Kernel.BabyMonster.Max15Run
import Certificates.Kernel.BabyMonster.HS.Facts17535
import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Certificates.Kernel.BabyMonster.Sound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Cbar.SimpleBase
public import CFSG.Monster.B.Max2.Pinned
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Pinned CFSG.Monster.B.Primes.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native in
theorem certificate17535 : CFSG.KC.BM.HS.Fact17535
    ((runG max15Prog glA₁ glA₂ 1 : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2))
    ((runG max15Prog glA₁ glA₂ 2 : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) := by
  have hA : ((CFSG.Monster.B.Pinned.glA₁ : GL (Fin 4370) (ZMod 2)) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = CFSG.KC.BM.stripMat CFSG.KC.BM.Seeds.A1 :=
    KernelBM.genA₁_eq_stripMat
  have hB : ((CFSG.Monster.B.Pinned.glA₂ : GL (Fin 4370) (ZMod 2)) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = CFSG.KC.BM.stripMat CFSG.KC.BM.Seeds.A2 :=
    KernelBM.genA₂_eq_stripMat
  rw [KernelBM.Max15Run.max15_g1 _ _ hA hB, KernelBM.Max15Run.max15_g2 _ _ hA hB]
  exact KernelBM.HS.fact17535

end Certificates
