module

public import CFSG.Monster.B.Pinned.Primes.Program
public import CFSG.Monster.B.Pinned.GeneratorDeterminants
import Certificates.Kernel.BabyMonster.PrimeOrd.Facts
import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Certificates.Kernel.BabyMonster.Sound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Max2.Pinned
public import CFSG.Open.Defs
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Primes.Native in
theorem certificate3160 :
    (wordG genA₁ genA₂ word7.toList ^ 1) ^ 7 = 1 ∧ wordG genA₁ genA₂ word7.toList ^ 1 ≠ 1 ∧
    (wordG genA₁ genA₂ word13.toList ^ 2) ^ 13 = 1 ∧ wordG genA₁ genA₂ word13.toList ^ 2 ≠ 1 ∧
    (wordG genA₁ genA₂ word17.toList ^ 2) ^ 17 = 1 ∧ wordG genA₁ genA₂ word17.toList ^ 2 ≠ 1 ∧
    (wordG genA₁ genA₂ word19.toList ^ 1) ^ 19 = 1 ∧ wordG genA₁ genA₂ word19.toList ^ 1 ≠ 1 ∧
    (wordG genA₁ genA₂ word31.toList ^ 1) ^ 31 = 1 ∧ wordG genA₁ genA₂ word31.toList ^ 1 ≠ 1 ∧
    (wordG genA₁ genA₂ word47.toList ^ 1) ^ 47 = 1 ∧ wordG genA₁ genA₂ word47.toList ^ 1 ≠ 1 := by
  rw [KernelBM.genA₁_eq_stripMat, KernelBM.genA₂_eq_stripMat]
  exact KernelBM.PrimeOrd.six_facts

end Certificates
