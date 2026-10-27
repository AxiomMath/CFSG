module

public import CFSG.Monster.Existence.Compat.Shapes
public import Certificates.Certificate3166Base
public import Certificates.Data.CFSGNative.MonsterB.BinaryElim
public import Certificates.Kernel.MonsterB.Tower3049Data

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Open
  CFSG.Blueprint

namespace CertificateChecks.Batch16014

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Open
  CFSG.Blueprint

private theorem toFacts_co2_card_0 : 42305421312000 = monsterCo2Order := by
  decide +kernel

private theorem toFacts_hn_card_1 : 273030912000000 = monsterHNOrder := by
  decide +kernel

end CertificateChecks.Batch16014

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Open
  CFSG.Blueprint in
theorem certificate16014 : (
    42305421312000 = monsterCo2Order
  ) ∧ (
    273030912000000 = monsterHNOrder
  ) := by
  exact ⟨CertificateChecks.Batch16014.toFacts_co2_card_0, CertificateChecks.Batch16014.toFacts_hn_card_1⟩

end Certificates
