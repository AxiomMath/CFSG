module

public import CFSG.Monster.B.Pinned.Primes.FiveWords
public import CFSG.RankThree.Native.BFiveHCheckInputs
public import Certificates.Certificate3109
import Certificates.Kernel.BabyMonster.Five.Facts
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

open CFSG.Monster.B.Pinned CFSG.RankThree.Native in
theorem certificate8120 : 
    (∀ i : Fin 4, hFive⁻¹ * qFive i * hFive =
      (List.ofFn fun j => qFive j ^ (bFiveHRows.getD i []).getD j 0).prod *
        zFive ^ bFiveHC.getD i 0) ∧
    hFive⁻¹ * zFive * hFive = zFive * zFive :=
  KernelBM.Five.fact8120

end Certificates
