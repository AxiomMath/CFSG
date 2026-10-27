module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWClsCheck

public section

namespace Certificates.Kernel.CensusW16

open CFSG.EvenSporadicStandard.Fin76b.W16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem zeta_ok : zetaCheck = true := by decide +kernel

theorem twist_ok : twistCheck = true := by decide +kernel

theorem fus_ok : fusCheck = true := by decide +kernel

theorem x45_ok : x45Check = true := by
  simp only [x45Check, sameSet, imgSet, Array.contains_eq_any_beq, ← Array.all_toList,
    ← Array.any_toList, Array.toList_map]
  decide +kernel

end Certificates.Kernel.CensusW16
