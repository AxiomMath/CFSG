
module

public import Certificates.Certificate441665Base

import Certificates.Kernel.HN1408.R0KGlue

public section

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
  CFSG.EvenSporadicStandard.HNRecog.HaradaLA Subgroup

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
  CFSG.EvenSporadicStandard.HNRecog.HaradaLA Subgroup in
theorem certificate441665 : Nat.card ↥P1408 = 177408000 → R0Facts := CFSG.KD.HN1408.R0K.r0FactsK

end Certificates
