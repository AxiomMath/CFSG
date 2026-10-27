module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKCases

public section

namespace CFSG.StandardType

@[expose] def GGSixRootCommKnownRest :
    Prop :=
  ∀ i : GGSixRCKRow, i ≠ .L32 → GGSixRootCommKnownRow i

theorem ggSixRootCommKnown_of_rest
    (h : GGSixRootCommKnownRest) : GGSixRootCommKnown :=
  ggSixRootCommKnown_iff_rows.mpr fun i =>
    if hi : i = .L32 then hi ▸ ggSixRootCommKnownRow_L32 else h i hi

end CFSG.StandardType
