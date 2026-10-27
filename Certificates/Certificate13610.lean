module

public import CFSG.Certificates.Kernel.BabyMonster.FiveAFacts
public import CFSG.Monster.B.Pinned.Primes.SeedGL
import CFSG.Monster.B.Final.SeedUnit
import Certificates.Kernel.BabyMonster.FiveA.Facts13610
import Certificates.Kernel.BabyMonster.Five.Regs
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

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Primes.Native

open CFSG.Monster.B.Pinned CFSG.Monster.B.Primes.Native in
theorem certificate13610 : CFSG.KC.BM.FiveA.Fact13610
    ((runG fiveProg glA₁ glA₂ 1 : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2))
    ((runG fiveProg glA₁ glA₂ 2 : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) := by
  have hR := bMat_runG_of_regsOK KernelBM.genA₁_eq_stripMat KernelBM.genA₂_eq_stripMat
    KernelBM.Five.five_regs
  have hX : ((runG fiveProg glA₁ glA₂ 1 : GL (Fin 4370) (ZMod 2)) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f85 := by
    rw [← bSeedGL_runG, coe_bSeedGL]
    exact hR 0 (by norm_num)
  have hH : ((runG fiveProg glA₁ glA₂ 2 : GL (Fin 4370) (ZMod 2)) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f86 := by
    rw [← bSeedGL_runG, coe_bSeedGL]
    exact hR 1 (by norm_num)
  rw [hX, hH]
  exact KernelBM.FiveA.fact13610

end Certificates
