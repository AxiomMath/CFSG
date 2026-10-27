module

public import CFSG.Monster.B.Pinned.Primes.ThreeWords
public import CFSG.Monster.B.Pinned.Primes.Data
public import Certificates.Certificate3109
import Certificates.Kernel.BabyMonster.Three.Facts
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
theorem certificate3161 : 
    xThree ^ 40 = 1 ∧ xThree ^ 20 ≠ 1 ∧ xThree ^ 8 ≠ 1 ∧ hThree ^ 8 = 1 ∧ hThree ^ 4 ≠ 1 ∧
      (∀ i, qThree i ^ 3 = 1 ∧ qThree i ≠ 1) ∧ zThree ^ 3 = 1 ∧ zThree ≠ 1 ∧
      (∀ i, qThree i * zThree = zThree * qThree i) ∧
      (∀ i j : Fin 8, i < j →
        bcomm (qThree i) (qThree j) = zThree ^ ((threeCommRows.getD i []).getD j 0)) ∧
      xThree⁻¹ * zThree * xThree = zThree * zThree ∧
      hThree⁻¹ * zThree * hThree = zThree * zThree ∧
      (∀ i : Fin 8, xThree⁻¹ * qThree i * xThree =
        (List.ofFn fun j => qThree j ^ (threeXRows.getD i []).getD j 0).prod *
          zThree ^ threeCVec.getD i 0) ∧
      ∀ i : Fin 8, hThree⁻¹ * qThree i * hThree =
        (List.ofFn fun j => qThree j ^ (threeYRows.getD i []).getD j 0).prod *
          zThree ^ threeDVec.getD i 0 :=
  KernelBM.Three.fact3161

end Certificates
