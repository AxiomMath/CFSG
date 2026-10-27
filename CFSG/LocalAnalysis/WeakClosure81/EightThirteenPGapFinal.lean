module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapU3F6
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapU3F4
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSL3F4
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4F6
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4F4
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Thm88)

theorem gapShapeFacts_holds :
    GapShapeFacts :=
  ⟨choiceOfKOn_shapeU3, choiceOfKOn_shapeL3, choiceOfKOn_shapeSp4, choiceOfKOn_shapeSL3,
    borelGL32SylowOn_shapeU3, borelGL32CenterOn_shapeL3, borelGL32CenterOn_shapeSp4,
    borelGL32CenterOn_shapeSL3⟩

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.WeakClosure81

end
