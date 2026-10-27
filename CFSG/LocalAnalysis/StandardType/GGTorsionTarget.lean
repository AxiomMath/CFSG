module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDatum
import CFSG.LocalAnalysis.StandardType.GGTablePThreeDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionTarget

theorem ggStdSubNotTorsionInput_of_known (h : GGTorsionKnown) : GGStdSubNotTorsionInput := by
  intro G _ _ p B x L D J hI hDJ hJ
  obtain ⟨δ, hdat⟩ := exists_ggTorsionDatum hI hDJ
  have hJL : J ≤ L := hDJ.1.2.2.2.2.2.1.1.trans inf_le_left
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  exact h p ↥L hst.1.1 δ (J.subgroupOf L) hdat
    (GGTablePThree.largeEvenMarking_subgroupOf hJL hJ)

end TorsionTarget

end CFSG.StandardType
