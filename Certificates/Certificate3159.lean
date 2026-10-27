module

public import CFSG.Monster.B.Pinned.Primes.FiveWords
public import CFSG.Monster.B.Pinned.Primes.Data
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

open CFSG.Monster.B.Pinned in
theorem certificate3159 : 
    xFive ^ 5 = 1 ∧ xFive ≠ 1 ∧ hFive ^ 8 = 1 ∧ hFive ^ 4 ≠ 1 ∧ wFive ^ 40 = 1 ∧
      wFive ^ 20 ≠ 1 ∧ wFive ^ 8 ≠ 1 ∧ (∀ i, qFive i ^ 5 = 1 ∧ qFive i ≠ 1) ∧ zFive ^ 5 = 1 ∧
      zFive ≠ 1 ∧ (∀ i, qFive i * zFive = zFive * qFive i) ∧
      (∀ i j : Fin 4, i < j →
        bcomm (qFive i) (qFive j) = zFive ^ ((fiveCommRows.getD i []).getD j 0)) ∧
      xFive * zFive = zFive * xFive ∧
      ∀ i : Fin 4, xFive⁻¹ * qFive i * xFive =
        (List.ofFn fun j => qFive j ^ (fiveActRows.getD i []).getD j 0).prod *
          zFive ^ fiveActC.getD i 0 :=
  KernelBM.Five.fact3159

end Certificates
