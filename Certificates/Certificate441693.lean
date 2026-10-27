module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab4Facts
import Certificates.Kernel.HN1408.Tab4ShapeFacts
import Certificates.Kernel.HN1408.Tab4PredFacts

public section

open CFSG.KD.HN1408.CbT CFSG.KD.HN1408.Tab4

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model in
theorem certificate441693 : Nat.card ↥P1408 = 177408000 → Tab4Facts := fun hP =>
    { stab_le := tab4_stab_le hP
      ne := tab4_ne
      ab := tab4_ab
      row0 := tab4_row0
      row1 := tab4_row1
      row2 := tab4_row2
      row3 := tab4_row3
      row4 := tab4_row4
      row5 := tab4_row5
      inj2 := tab4_inj2 hP
      inj4 := tab4_inj4 hP
      inj5 := tab4_inj5 hP }

end Certificates
