module

public import CFSG.Open.MonsterDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.Existence.Compat.U62Center
public import Certificates.Certificate3166Base
import CFSG.Adapters.ProjectiveSpecialLinear
import Certificates.Kernel.SporSch.Th.Cent

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Open
  CFSG.Blueprint

namespace CertificateChecks.Batch16012

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Open
  CFSG.Blueprint

private theorem card_nativeTh_0 : 90745943887872000 = monsterThOrder := by
  decide +kernel

private theorem card_u62_of_lieModel_1 :
    (2 ^ 1) ^ (6 * (6 - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 6, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
          Nat.gcd 6 (2 ^ 1 + 1) = ordTwistedA 5 2 := by
  decide +kernel

private theorem twoARemaining_fi23_card_2 : 4089470473293004800 = monsterFi23Order := by
  decide +kernel

private theorem twoARemaining_mcl_card_3 : 898128000 = monsterMcLOrder := by
  decide +kernel

private theorem twoARemaining_fi22_card_4 : 64561751654400 = monsterFi22Order := by
  decide +kernel

end CertificateChecks.Batch16012

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Open
  CFSG.Blueprint in
theorem certificate16012 : (
    90745943887872000 = monsterThOrder
  ) ∧ (
    (2 ^ 1) ^ (6 * (6 - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 6, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
          Nat.gcd 6 (2 ^ 1 + 1) = ordTwistedA 5 2
  ) ∧ (
    4089470473293004800 = monsterFi23Order
  ) ∧ (
    898128000 = monsterMcLOrder
  ) ∧ (
    64561751654400 = monsterFi22Order
  ) := by
  exact ⟨CertificateChecks.Batch16012.card_nativeTh_0, CertificateChecks.Batch16012.card_u62_of_lieModel_1,
    CertificateChecks.Batch16012.twoARemaining_fi23_card_2, CertificateChecks.Batch16012.twoARemaining_mcl_card_3,
    CertificateChecks.Batch16012.twoARemaining_fi22_card_4⟩

end Certificates
