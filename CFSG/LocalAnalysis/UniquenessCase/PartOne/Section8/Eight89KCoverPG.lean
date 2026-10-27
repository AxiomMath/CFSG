module

public import Certificates.Data.Eight89KCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

abbrev CoverPG (n i j k l : ℕ) : Type :=
  CFSG.CosetTable.PG 3 (KData.coverWords n i j k l)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
