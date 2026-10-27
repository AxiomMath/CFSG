module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row8.Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row8.Pos
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row8.Size
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row8.Class
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row8.Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

theorem row8_holds (F : Type) [Field F] [Fintype F] [DecidableEq F] : Row8 F := by
  intro hF b c hbc α hα e f u v z₀ t₀ hz ht
  exact matrixRowData_stdComp
    (row8_facts F hF b c hbc α hα z₀ t₀ hz ht)
    (row8_pos F hF b c hbc α hα z₀ t₀ hz ht)
    (row8_size F hF b c hbc α hα z₀ t₀ hz ht)
    (row8_class F hF b c hbc α hα z₀ t₀ hz ht)
    (row8_gen F hF b c hbc α hα z₀ t₀ hz ht)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
