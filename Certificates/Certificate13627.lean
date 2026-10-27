module

public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Struct
public import CFSG.Monster.B.Pinned.Primes.FiveWords
public import Certificates.Certificate3109
import Certificates.Kernel.BabyMonster.FiveA.CoverB
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Certificates.Kernel.BabyMonster.Sound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Cbar.SimpleBase
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.Max2.Pinned
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.KC.BM.PcFive in
theorem certificate13627 : ∀ i ∈ [3125, 3126, 3127],
    ∃ W : CFSG.Blueprint.NativeSporadic.B, W * W = 1 ∧ W ≠ 1 ∧ (bMat W - 1).rank = 2048 ∧
      W * psi xFive (qW xFive hFive) (zW xFive hFive) (dec i) =
        psi xFive (qW xFive hFive) (zW xFive hFive) (dec i) * W :=
  KernelBM.FiveA.wits13627

end Certificates
