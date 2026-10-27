module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedF1
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedF2
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedF3Model
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedCenter
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedU3
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedSp4
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedL3AB
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedL3C

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem involutionCentralizerOn_shapeU3 : InvolutionCentralizerOn ShapeU3 :=
  involutionCentralizerOn_of_facts ShapeU3 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => outerFixedNotElem_isU3 (isU3_centerQuotient_of_shapeU3 h))

theorem involutionCentralizerOn_shapeL3 : InvolutionCentralizerOn ShapeL3 :=
  involutionCentralizerOn_of_facts ShapeL3 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => outerFixedNotElem_isL3 (isL3_centerQuotient_of_shapeL3 h))

theorem involutionCentralizerOn_shapeSp4 : InvolutionCentralizerOn ShapeSp4 :=
  involutionCentralizerOn_of_facts ShapeSp4 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => outerFixedNotElem_isSp4 (isSp4_centerQuotient_of_shapeSp4 h))

theorem involutionCentralizerOn_shapeSL3 : InvolutionCentralizerOn ShapeSL3 :=
  involutionCentralizerOn_of_facts ShapeSL3 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => outerFixedNotElem_isL3 h.2.2)

theorem fourGroupInnerOn_shapeU3 : FourGroupInnerOn ShapeU3 :=
  fourGroupInnerOn_of_facts ShapeU3 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => outerFixedNoNormalTwo_isU3 (isU3_centerQuotient_of_shapeU3 h))
    (fun _ _ _ _ h => outerFixedRigid_isU3 (isU3_centerQuotient_of_shapeU3 h))

theorem fourGroupInnerOn_shapeL3 : FourGroupInnerOn ShapeL3 :=
  fourGroupInnerOn_of_facts ShapeL3 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => outerFixedNoNormalTwo_isL3 (isL3_centerQuotient_of_shapeL3 h))
    (fun _ _ _ _ h => outerFixedRigid_isL3 (isL3_centerQuotient_of_shapeL3 h))

theorem fourGroupInnerOn_shapeSp4 : FourGroupInnerOn ShapeSp4 :=
  fourGroupInnerOn_of_facts ShapeSp4 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => outerFixedNoNormalTwo_isSp4 (isSp4_centerQuotient_of_shapeSp4 h))
    (fun _ _ _ _ h => outerFixedRigid_isSp4 (isSp4_centerQuotient_of_shapeSp4 h))

theorem fourGroupInnerOn_shapeSL3 : FourGroupInnerOn ShapeSL3 :=
  fourGroupInnerOn_of_facts ShapeSL3 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => outerFixedNoNormalTwo_isL3 h.2.2)
    (fun _ _ _ _ h => outerFixedRigid_isL3 h.2.2)

theorem borelRankTwoOn_shapeL3 : BorelRankTwoOn ShapeL3 :=
  borelRankTwoOn_of_quotient ShapeL3 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => borelRankTwoTop_of_isL3 (isL3_centerQuotient_of_shapeL3 h))

theorem borelRankTwoOn_shapeSp4 : BorelRankTwoOn ShapeSp4 :=
  borelRankTwoOn_of_quotient ShapeSp4 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => borelRankTwoTop_of_isSp4 (isSp4_centerQuotient_of_shapeSp4 h))

theorem borelRankTwoOn_shapeSL3 : BorelRankTwoOn ShapeSL3 :=
  borelRankTwoOn_of_quotient ShapeSL3 (fun _ _ _ _ h => h.1)
    (fun _ _ _ _ h => borelRankTwoTop_of_isL3 h.2.2)

theorem citedShapeFacts_holds : CitedShapeFacts :=
  ⟨involutionCentralizerOn_shapeU3, involutionCentralizerOn_shapeL3,
    involutionCentralizerOn_shapeSp4, involutionCentralizerOn_shapeSL3,
    fourGroupInnerOn_shapeU3, fourGroupInnerOn_shapeL3, fourGroupInnerOn_shapeSp4,
    fourGroupInnerOn_shapeSL3, borelRankTwoOn_shapeL3, borelRankTwoOn_shapeSp4,
    borelRankTwoOn_shapeSL3⟩

end CFSG.LocalAnalysis.WeakClosure81

end
