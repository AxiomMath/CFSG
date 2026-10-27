module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Facts
import Certificates.Kernel.HN1408.Tab6ShapeFacts
import Certificates.Kernel.HN1408.Tab6PredFacts

public section

open CFSG.KD.HN1408.Tab6

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model in
theorem certificate441694 : Nat.card ↥P1408 = 177408000 → Tab6Facts := fun hP =>
    { stab_le := tab6_stab_le hP
      ne := tab6_ne
      row0 := tab6_row0
      row1 := tab6_row1
      row2 := tab6_row2
      row3 := tab6_row3
      row4 := tab6_row4
      row5 := tab6_row5
      row6 := tab6_row6
      row7 := tab6_row7
      sub2 := tab6_sub2
      sub4 := tab6_sub4
      sub6 := tab6_sub6
      sub7 := tab6_sub7
      shape2 := tab6_shape2
      shape4 := tab6_shape4
      shape6 := tab6_shape6
      shape7 := tab6_shape7
      mem5A := tab6_mem5A }

end Certificates
