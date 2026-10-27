
module

public import Certificates.Certificate26771Base

import Certificates.Kernel.HN1408.InvClassK
import Certificates.Kernel.HN1408.ClsAZFacts

public section

open CFSG.EvenSporadicStandard.HNRecog

namespace Certificates

end Certificates

public section

open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog in
theorem certificate26771 : Nat.card ↥P1408 = 177408000 → InvClassFacts := fun hP =>
    have hz := CzT.czT_eq hP
    have haz := ClsR.az_facts hP
    have hb := ClsR.b_facts hP
    have hz₁ := Cz1T.z1_facts hP
    { z := ⟨CzT.class_z_card hP, hz.1 ▸ hz.2, hz.1⟩
      az := ⟨haz.1, haz.2.1, haz.2.2⟩
      b := ⟨hb.1, hb.2.1, hb.2.2⟩
      z₁ := ⟨hz₁.1, hz₁.2.1, hz₁.2.2⟩
      not_isConj := CzInv.not_isConj_K hP
      cover := CzInv.involution_cover_K hP }

end Certificates
