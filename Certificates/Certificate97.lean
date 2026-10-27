module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnessesCore

public section

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

namespace CertificateChecks.Batch97

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem c8FourActionRecord64_covered : c8FourActionCovered c8FourRecordData64 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord64_bounded : c8FourActionBounded c8FourRecordData64 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord65_covered : c8FourActionCovered c8FourRecordData65 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord65_bounded : c8FourActionBounded c8FourRecordData65 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord66_covered : c8FourActionCovered c8FourRecordData66 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨3, ?_⟩
  decide +kernel

private theorem c8FourActionRecord66_bounded : c8FourActionBounded c8FourRecordData66 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord67_covered : c8FourActionCovered c8FourRecordData67 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord67_bounded : c8FourActionBounded c8FourRecordData67 := by
  decide +kernel

private theorem c8FourActionRecord68_covered : c8FourActionCovered c8FourRecordData68 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord68_bounded : c8FourActionBounded c8FourRecordData68 := by
  decide +kernel

private theorem c8FourActionRecord69_covered : c8FourActionCovered c8FourRecordData69 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord69_bounded : c8FourActionBounded c8FourRecordData69 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord70_covered : c8FourActionCovered c8FourRecordData70 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord70_bounded : c8FourActionBounded c8FourRecordData70 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord71_covered : c8FourActionCovered c8FourRecordData71 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord71_bounded : c8FourActionBounded c8FourRecordData71 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord72_covered : c8FourActionCovered c8FourRecordData72 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord72_bounded : c8FourActionBounded c8FourRecordData72 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord73_covered : c8FourActionCovered c8FourRecordData73 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord73_bounded : c8FourActionBounded c8FourRecordData73 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord74_covered : c8FourActionCovered c8FourRecordData74 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord74_bounded : c8FourActionBounded c8FourRecordData74 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord75_covered : c8FourActionCovered c8FourRecordData75 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord75_bounded : c8FourActionBounded c8FourRecordData75 := by
  decide +kernel

private theorem c8FourActionRecord76_covered : c8FourActionCovered c8FourRecordData76 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord76_bounded : c8FourActionBounded c8FourRecordData76 := by
  decide +kernel

private theorem c8FourActionRecord77_covered : c8FourActionCovered c8FourRecordData77 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨3, ?_⟩
  decide +kernel

private theorem c8FourActionRecord77_bounded : c8FourActionBounded c8FourRecordData77 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord78_covered : c8FourActionCovered c8FourRecordData78 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord78_bounded : c8FourActionBounded c8FourRecordData78 := by
  decide +kernel

private theorem c8FourActionRecord79_covered : c8FourActionCovered c8FourRecordData79 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord79_bounded : c8FourActionBounded c8FourRecordData79 := by
  decide +kernel

private theorem c8FourActionRecord80_covered : c8FourActionCovered c8FourRecordData80 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord80_bounded : c8FourActionBounded c8FourRecordData80 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord81_covered : c8FourActionCovered c8FourRecordData81 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord81_bounded : c8FourActionBounded c8FourRecordData81 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord82_covered : c8FourActionCovered c8FourRecordData82 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord82_bounded : c8FourActionBounded c8FourRecordData82 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord83_covered : c8FourActionCovered c8FourRecordData83 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord83_bounded : c8FourActionBounded c8FourRecordData83 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord84_covered : c8FourActionCovered c8FourRecordData84 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord84_bounded : c8FourActionBounded c8FourRecordData84 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord85_covered : c8FourActionCovered c8FourRecordData85 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨3, ?_⟩
  decide +kernel

private theorem c8FourActionRecord85_bounded : c8FourActionBounded c8FourRecordData85 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord86_covered : c8FourActionCovered c8FourRecordData86 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord86_bounded : c8FourActionBounded c8FourRecordData86 := by
  decide +kernel

private theorem c8FourActionRecord87_covered : c8FourActionCovered c8FourRecordData87 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord87_bounded : c8FourActionBounded c8FourRecordData87 := by
  decide +kernel

private theorem c8FourActionRecord88_covered : c8FourActionCovered c8FourRecordData88 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord88_bounded : c8FourActionBounded c8FourRecordData88 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord89_covered : c8FourActionCovered c8FourRecordData89 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord89_bounded : c8FourActionBounded c8FourRecordData89 := by
  decide +kernel

private theorem c8FourActionRecord90_covered : c8FourActionCovered c8FourRecordData90 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord90_bounded : c8FourActionBounded c8FourRecordData90 := by
  decide +kernel

private theorem c8FourActionRecord91_covered : c8FourActionCovered c8FourRecordData91 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨3, ?_⟩
  decide +kernel

private theorem c8FourActionRecord91_bounded : c8FourActionBounded c8FourRecordData91 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord92_covered : c8FourActionCovered c8FourRecordData92 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord92_bounded : c8FourActionBounded c8FourRecordData92 := by
  decide +kernel

private theorem c8FourActionRecord93_covered : c8FourActionCovered c8FourRecordData93 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord93_bounded : c8FourActionBounded c8FourRecordData93 := by
  decide +kernel

private theorem c8FourActionRecord94_covered : c8FourActionCovered c8FourRecordData94 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨3, ?_⟩
  decide +kernel

private theorem c8FourActionRecord94_bounded : c8FourActionBounded c8FourRecordData94 := by
  decide +kernel

private theorem c8FourActionRecord95_covered : c8FourActionCovered c8FourRecordData95 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord95_bounded : c8FourActionBounded c8FourRecordData95 := by
  decide +kernel

private theorem c8FourActionRecord96_covered : c8FourActionCovered c8FourRecordData96 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord96_bounded : c8FourActionBounded c8FourRecordData96 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord97_covered : c8FourActionCovered c8FourRecordData97 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord97_bounded : c8FourActionBounded c8FourRecordData97 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord98_covered : c8FourActionCovered c8FourRecordData98 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord98_bounded : c8FourActionBounded c8FourRecordData98 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord99_covered : c8FourActionCovered c8FourRecordData99 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord99_bounded : c8FourActionBounded c8FourRecordData99 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord100_covered : c8FourActionCovered c8FourRecordData100 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord100_bounded : c8FourActionBounded c8FourRecordData100 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord101_covered : c8FourActionCovered c8FourRecordData101 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord101_bounded : c8FourActionBounded c8FourRecordData101 := by
  decide +kernel

private theorem c8FourActionRecord102_covered : c8FourActionCovered c8FourRecordData102 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord102_bounded : c8FourActionBounded c8FourRecordData102 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord103_covered : c8FourActionCovered c8FourRecordData103 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord103_bounded : c8FourActionBounded c8FourRecordData103 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord104_covered : c8FourActionCovered c8FourRecordData104 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord104_bounded : c8FourActionBounded c8FourRecordData104 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord105_covered : c8FourActionCovered c8FourRecordData105 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord105_bounded : c8FourActionBounded c8FourRecordData105 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord106_covered : c8FourActionCovered c8FourRecordData106 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord106_bounded : c8FourActionBounded c8FourRecordData106 := by
  decide +kernel

private theorem c8FourActionRecord107_covered : c8FourActionCovered c8FourRecordData107 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨52, ?_⟩
  decide +kernel

private theorem c8FourActionRecord107_bounded : c8FourActionBounded c8FourRecordData107 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord108_covered : c8FourActionCovered c8FourRecordData108 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨52, ?_⟩
  decide +kernel

private theorem c8FourActionRecord108_bounded : c8FourActionBounded c8FourRecordData108 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord109_covered : c8FourActionCovered c8FourRecordData109 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord109_bounded : c8FourActionBounded c8FourRecordData109 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord110_covered : c8FourActionCovered c8FourRecordData110 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨6, ?_⟩
  decide +kernel

private theorem c8FourActionRecord110_bounded : c8FourActionBounded c8FourRecordData110 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord111_covered : c8FourActionCovered c8FourRecordData111 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord111_bounded : c8FourActionBounded c8FourRecordData111 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord112_covered : c8FourActionCovered c8FourRecordData112 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord112_bounded : c8FourActionBounded c8FourRecordData112 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord113_covered : c8FourActionCovered c8FourRecordData113 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord113_bounded : c8FourActionBounded c8FourRecordData113 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord114_covered : c8FourActionCovered c8FourRecordData114 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord114_bounded : c8FourActionBounded c8FourRecordData114 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord115_covered : c8FourActionCovered c8FourRecordData115 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord115_bounded : c8FourActionBounded c8FourRecordData115 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord116_covered : c8FourActionCovered c8FourRecordData116 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨6, ?_⟩
  decide +kernel

private theorem c8FourActionRecord116_bounded : c8FourActionBounded c8FourRecordData116 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord117_covered : c8FourActionCovered c8FourRecordData117 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨24, ?_⟩
  decide +kernel

private theorem c8FourActionRecord117_bounded : c8FourActionBounded c8FourRecordData117 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord118_covered : c8FourActionCovered c8FourRecordData118 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord118_bounded : c8FourActionBounded c8FourRecordData118 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord119_covered : c8FourActionCovered c8FourRecordData119 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord119_bounded : c8FourActionBounded c8FourRecordData119 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord120_covered : c8FourActionCovered c8FourRecordData120 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨12, ?_⟩
  decide +kernel

private theorem c8FourActionRecord120_bounded : c8FourActionBounded c8FourRecordData120 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord121_covered : c8FourActionCovered c8FourRecordData121 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord121_bounded : c8FourActionBounded c8FourRecordData121 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord122_covered : c8FourActionCovered c8FourRecordData122 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord122_bounded : c8FourActionBounded c8FourRecordData122 := by
  decide +kernel

private theorem c8FourActionRecord123_covered : c8FourActionCovered c8FourRecordData123 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord123_bounded : c8FourActionBounded c8FourRecordData123 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord124_covered : c8FourActionCovered c8FourRecordData124 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord124_bounded : c8FourActionBounded c8FourRecordData124 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord125_covered : c8FourActionCovered c8FourRecordData125 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨14, ?_⟩
  decide +kernel

private theorem c8FourActionRecord125_bounded : c8FourActionBounded c8FourRecordData125 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord126_covered : c8FourActionCovered c8FourRecordData126 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord126_bounded : c8FourActionBounded c8FourRecordData126 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord127_covered : c8FourActionCovered c8FourRecordData127 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨13, ?_⟩
  decide +kernel

private theorem c8FourActionRecord127_bounded : c8FourActionBounded c8FourRecordData127 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionChunk1_covered (j : Fin 64) :
    c8FourActionCovered (c8FourRecordChunk1[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord64_covered
  · exact c8FourActionRecord65_covered
  · exact c8FourActionRecord66_covered
  · exact c8FourActionRecord67_covered
  · exact c8FourActionRecord68_covered
  · exact c8FourActionRecord69_covered
  · exact c8FourActionRecord70_covered
  · exact c8FourActionRecord71_covered
  · exact c8FourActionRecord72_covered
  · exact c8FourActionRecord73_covered
  · exact c8FourActionRecord74_covered
  · exact c8FourActionRecord75_covered
  · exact c8FourActionRecord76_covered
  · exact c8FourActionRecord77_covered
  · exact c8FourActionRecord78_covered
  · exact c8FourActionRecord79_covered
  · exact c8FourActionRecord80_covered
  · exact c8FourActionRecord81_covered
  · exact c8FourActionRecord82_covered
  · exact c8FourActionRecord83_covered
  · exact c8FourActionRecord84_covered
  · exact c8FourActionRecord85_covered
  · exact c8FourActionRecord86_covered
  · exact c8FourActionRecord87_covered
  · exact c8FourActionRecord88_covered
  · exact c8FourActionRecord89_covered
  · exact c8FourActionRecord90_covered
  · exact c8FourActionRecord91_covered
  · exact c8FourActionRecord92_covered
  · exact c8FourActionRecord93_covered
  · exact c8FourActionRecord94_covered
  · exact c8FourActionRecord95_covered
  · exact c8FourActionRecord96_covered
  · exact c8FourActionRecord97_covered
  · exact c8FourActionRecord98_covered
  · exact c8FourActionRecord99_covered
  · exact c8FourActionRecord100_covered
  · exact c8FourActionRecord101_covered
  · exact c8FourActionRecord102_covered
  · exact c8FourActionRecord103_covered
  · exact c8FourActionRecord104_covered
  · exact c8FourActionRecord105_covered
  · exact c8FourActionRecord106_covered
  · exact c8FourActionRecord107_covered
  · exact c8FourActionRecord108_covered
  · exact c8FourActionRecord109_covered
  · exact c8FourActionRecord110_covered
  · exact c8FourActionRecord111_covered
  · exact c8FourActionRecord112_covered
  · exact c8FourActionRecord113_covered
  · exact c8FourActionRecord114_covered
  · exact c8FourActionRecord115_covered
  · exact c8FourActionRecord116_covered
  · exact c8FourActionRecord117_covered
  · exact c8FourActionRecord118_covered
  · exact c8FourActionRecord119_covered
  · exact c8FourActionRecord120_covered
  · exact c8FourActionRecord121_covered
  · exact c8FourActionRecord122_covered
  · exact c8FourActionRecord123_covered
  · exact c8FourActionRecord124_covered
  · exact c8FourActionRecord125_covered
  · exact c8FourActionRecord126_covered
  · exact c8FourActionRecord127_covered

private theorem c8FourActionChunk1_bounded (j : Fin 64) :
    c8FourActionBounded (c8FourRecordChunk1[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord64_bounded
  · exact c8FourActionRecord65_bounded
  · exact c8FourActionRecord66_bounded
  · exact c8FourActionRecord67_bounded
  · exact c8FourActionRecord68_bounded
  · exact c8FourActionRecord69_bounded
  · exact c8FourActionRecord70_bounded
  · exact c8FourActionRecord71_bounded
  · exact c8FourActionRecord72_bounded
  · exact c8FourActionRecord73_bounded
  · exact c8FourActionRecord74_bounded
  · exact c8FourActionRecord75_bounded
  · exact c8FourActionRecord76_bounded
  · exact c8FourActionRecord77_bounded
  · exact c8FourActionRecord78_bounded
  · exact c8FourActionRecord79_bounded
  · exact c8FourActionRecord80_bounded
  · exact c8FourActionRecord81_bounded
  · exact c8FourActionRecord82_bounded
  · exact c8FourActionRecord83_bounded
  · exact c8FourActionRecord84_bounded
  · exact c8FourActionRecord85_bounded
  · exact c8FourActionRecord86_bounded
  · exact c8FourActionRecord87_bounded
  · exact c8FourActionRecord88_bounded
  · exact c8FourActionRecord89_bounded
  · exact c8FourActionRecord90_bounded
  · exact c8FourActionRecord91_bounded
  · exact c8FourActionRecord92_bounded
  · exact c8FourActionRecord93_bounded
  · exact c8FourActionRecord94_bounded
  · exact c8FourActionRecord95_bounded
  · exact c8FourActionRecord96_bounded
  · exact c8FourActionRecord97_bounded
  · exact c8FourActionRecord98_bounded
  · exact c8FourActionRecord99_bounded
  · exact c8FourActionRecord100_bounded
  · exact c8FourActionRecord101_bounded
  · exact c8FourActionRecord102_bounded
  · exact c8FourActionRecord103_bounded
  · exact c8FourActionRecord104_bounded
  · exact c8FourActionRecord105_bounded
  · exact c8FourActionRecord106_bounded
  · exact c8FourActionRecord107_bounded
  · exact c8FourActionRecord108_bounded
  · exact c8FourActionRecord109_bounded
  · exact c8FourActionRecord110_bounded
  · exact c8FourActionRecord111_bounded
  · exact c8FourActionRecord112_bounded
  · exact c8FourActionRecord113_bounded
  · exact c8FourActionRecord114_bounded
  · exact c8FourActionRecord115_bounded
  · exact c8FourActionRecord116_bounded
  · exact c8FourActionRecord117_bounded
  · exact c8FourActionRecord118_bounded
  · exact c8FourActionRecord119_bounded
  · exact c8FourActionRecord120_bounded
  · exact c8FourActionRecord121_bounded
  · exact c8FourActionRecord122_bounded
  · exact c8FourActionRecord123_bounded
  · exact c8FourActionRecord124_bounded
  · exact c8FourActionRecord125_bounded
  · exact c8FourActionRecord126_bounded
  · exact c8FourActionRecord127_bounded

end CertificateChecks.Batch97

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers in
theorem certificate97 : (c8FourActionCovered c8FourRecordData64)
    ∧ (c8FourActionBounded c8FourRecordData64)
    ∧ (c8FourActionCovered c8FourRecordData65)
    ∧ (c8FourActionBounded c8FourRecordData65)
    ∧ (c8FourActionCovered c8FourRecordData66)
    ∧ (c8FourActionBounded c8FourRecordData66)
    ∧ (c8FourActionCovered c8FourRecordData67)
    ∧ (c8FourActionBounded c8FourRecordData67)
    ∧ (c8FourActionCovered c8FourRecordData68)
    ∧ (c8FourActionBounded c8FourRecordData68)
    ∧ (c8FourActionCovered c8FourRecordData69)
    ∧ (c8FourActionBounded c8FourRecordData69)
    ∧ (c8FourActionCovered c8FourRecordData70)
    ∧ (c8FourActionBounded c8FourRecordData70)
    ∧ (c8FourActionCovered c8FourRecordData71)
    ∧ (c8FourActionBounded c8FourRecordData71)
    ∧ (c8FourActionCovered c8FourRecordData72)
    ∧ (c8FourActionBounded c8FourRecordData72)
    ∧ (c8FourActionCovered c8FourRecordData73)
    ∧ (c8FourActionBounded c8FourRecordData73)
    ∧ (c8FourActionCovered c8FourRecordData74)
    ∧ (c8FourActionBounded c8FourRecordData74)
    ∧ (c8FourActionCovered c8FourRecordData75)
    ∧ (c8FourActionBounded c8FourRecordData75)
    ∧ (c8FourActionCovered c8FourRecordData76)
    ∧ (c8FourActionBounded c8FourRecordData76)
    ∧ (c8FourActionCovered c8FourRecordData77)
    ∧ (c8FourActionBounded c8FourRecordData77)
    ∧ (c8FourActionCovered c8FourRecordData78)
    ∧ (c8FourActionBounded c8FourRecordData78)
    ∧ (c8FourActionCovered c8FourRecordData79)
    ∧ (c8FourActionBounded c8FourRecordData79)
    ∧ (c8FourActionCovered c8FourRecordData80)
    ∧ (c8FourActionBounded c8FourRecordData80)
    ∧ (c8FourActionCovered c8FourRecordData81)
    ∧ (c8FourActionBounded c8FourRecordData81)
    ∧ (c8FourActionCovered c8FourRecordData82)
    ∧ (c8FourActionBounded c8FourRecordData82)
    ∧ (c8FourActionCovered c8FourRecordData83)
    ∧ (c8FourActionBounded c8FourRecordData83)
    ∧ (c8FourActionCovered c8FourRecordData84)
    ∧ (c8FourActionBounded c8FourRecordData84)
    ∧ (c8FourActionCovered c8FourRecordData85)
    ∧ (c8FourActionBounded c8FourRecordData85)
    ∧ (c8FourActionCovered c8FourRecordData86)
    ∧ (c8FourActionBounded c8FourRecordData86)
    ∧ (c8FourActionCovered c8FourRecordData87)
    ∧ (c8FourActionBounded c8FourRecordData87)
    ∧ (c8FourActionCovered c8FourRecordData88)
    ∧ (c8FourActionBounded c8FourRecordData88)
    ∧ (c8FourActionCovered c8FourRecordData89)
    ∧ (c8FourActionBounded c8FourRecordData89)
    ∧ (c8FourActionCovered c8FourRecordData90)
    ∧ (c8FourActionBounded c8FourRecordData90)
    ∧ (c8FourActionCovered c8FourRecordData91)
    ∧ (c8FourActionBounded c8FourRecordData91)
    ∧ (c8FourActionCovered c8FourRecordData92)
    ∧ (c8FourActionBounded c8FourRecordData92)
    ∧ (c8FourActionCovered c8FourRecordData93)
    ∧ (c8FourActionBounded c8FourRecordData93)
    ∧ (c8FourActionCovered c8FourRecordData94)
    ∧ (c8FourActionBounded c8FourRecordData94)
    ∧ (c8FourActionCovered c8FourRecordData95)
    ∧ (c8FourActionBounded c8FourRecordData95)
    ∧ (c8FourActionCovered c8FourRecordData96)
    ∧ (c8FourActionBounded c8FourRecordData96)
    ∧ (c8FourActionCovered c8FourRecordData97)
    ∧ (c8FourActionBounded c8FourRecordData97)
    ∧ (c8FourActionCovered c8FourRecordData98)
    ∧ (c8FourActionBounded c8FourRecordData98)
    ∧ (c8FourActionCovered c8FourRecordData99)
    ∧ (c8FourActionBounded c8FourRecordData99)
    ∧ (c8FourActionCovered c8FourRecordData100)
    ∧ (c8FourActionBounded c8FourRecordData100)
    ∧ (c8FourActionCovered c8FourRecordData101)
    ∧ (c8FourActionBounded c8FourRecordData101)
    ∧ (c8FourActionCovered c8FourRecordData102)
    ∧ (c8FourActionBounded c8FourRecordData102)
    ∧ (c8FourActionCovered c8FourRecordData103)
    ∧ (c8FourActionBounded c8FourRecordData103)
    ∧ (c8FourActionCovered c8FourRecordData104)
    ∧ (c8FourActionBounded c8FourRecordData104)
    ∧ (c8FourActionCovered c8FourRecordData105)
    ∧ (c8FourActionBounded c8FourRecordData105)
    ∧ (c8FourActionCovered c8FourRecordData106)
    ∧ (c8FourActionBounded c8FourRecordData106)
    ∧ (c8FourActionCovered c8FourRecordData107)
    ∧ (c8FourActionBounded c8FourRecordData107)
    ∧ (c8FourActionCovered c8FourRecordData108)
    ∧ (c8FourActionBounded c8FourRecordData108)
    ∧ (c8FourActionCovered c8FourRecordData109)
    ∧ (c8FourActionBounded c8FourRecordData109)
    ∧ (c8FourActionCovered c8FourRecordData110)
    ∧ (c8FourActionBounded c8FourRecordData110)
    ∧ (c8FourActionCovered c8FourRecordData111)
    ∧ (c8FourActionBounded c8FourRecordData111)
    ∧ (c8FourActionCovered c8FourRecordData112)
    ∧ (c8FourActionBounded c8FourRecordData112)
    ∧ (c8FourActionCovered c8FourRecordData113)
    ∧ (c8FourActionBounded c8FourRecordData113)
    ∧ (c8FourActionCovered c8FourRecordData114)
    ∧ (c8FourActionBounded c8FourRecordData114)
    ∧ (c8FourActionCovered c8FourRecordData115)
    ∧ (c8FourActionBounded c8FourRecordData115)
    ∧ (c8FourActionCovered c8FourRecordData116)
    ∧ (c8FourActionBounded c8FourRecordData116)
    ∧ (c8FourActionCovered c8FourRecordData117)
    ∧ (c8FourActionBounded c8FourRecordData117)
    ∧ (c8FourActionCovered c8FourRecordData118)
    ∧ (c8FourActionBounded c8FourRecordData118)
    ∧ (c8FourActionCovered c8FourRecordData119)
    ∧ (c8FourActionBounded c8FourRecordData119)
    ∧ (c8FourActionCovered c8FourRecordData120)
    ∧ (c8FourActionBounded c8FourRecordData120)
    ∧ (c8FourActionCovered c8FourRecordData121)
    ∧ (c8FourActionBounded c8FourRecordData121)
    ∧ (c8FourActionCovered c8FourRecordData122)
    ∧ (c8FourActionBounded c8FourRecordData122)
    ∧ (c8FourActionCovered c8FourRecordData123)
    ∧ (c8FourActionBounded c8FourRecordData123)
    ∧ (c8FourActionCovered c8FourRecordData124)
    ∧ (c8FourActionBounded c8FourRecordData124)
    ∧ (c8FourActionCovered c8FourRecordData125)
    ∧ (c8FourActionBounded c8FourRecordData125)
    ∧ (c8FourActionCovered c8FourRecordData126)
    ∧ (c8FourActionBounded c8FourRecordData126)
    ∧ (c8FourActionCovered c8FourRecordData127)
    ∧ (c8FourActionBounded c8FourRecordData127) := by
  exact ⟨CertificateChecks.Batch97.c8FourActionRecord64_covered, CertificateChecks.Batch97.c8FourActionRecord64_bounded, CertificateChecks.Batch97.c8FourActionRecord65_covered, CertificateChecks.Batch97.c8FourActionRecord65_bounded, CertificateChecks.Batch97.c8FourActionRecord66_covered, CertificateChecks.Batch97.c8FourActionRecord66_bounded, CertificateChecks.Batch97.c8FourActionRecord67_covered, CertificateChecks.Batch97.c8FourActionRecord67_bounded, CertificateChecks.Batch97.c8FourActionRecord68_covered, CertificateChecks.Batch97.c8FourActionRecord68_bounded, CertificateChecks.Batch97.c8FourActionRecord69_covered, CertificateChecks.Batch97.c8FourActionRecord69_bounded, CertificateChecks.Batch97.c8FourActionRecord70_covered, CertificateChecks.Batch97.c8FourActionRecord70_bounded, CertificateChecks.Batch97.c8FourActionRecord71_covered, CertificateChecks.Batch97.c8FourActionRecord71_bounded, CertificateChecks.Batch97.c8FourActionRecord72_covered, CertificateChecks.Batch97.c8FourActionRecord72_bounded, CertificateChecks.Batch97.c8FourActionRecord73_covered, CertificateChecks.Batch97.c8FourActionRecord73_bounded, CertificateChecks.Batch97.c8FourActionRecord74_covered, CertificateChecks.Batch97.c8FourActionRecord74_bounded, CertificateChecks.Batch97.c8FourActionRecord75_covered, CertificateChecks.Batch97.c8FourActionRecord75_bounded, CertificateChecks.Batch97.c8FourActionRecord76_covered, CertificateChecks.Batch97.c8FourActionRecord76_bounded, CertificateChecks.Batch97.c8FourActionRecord77_covered, CertificateChecks.Batch97.c8FourActionRecord77_bounded, CertificateChecks.Batch97.c8FourActionRecord78_covered, CertificateChecks.Batch97.c8FourActionRecord78_bounded, CertificateChecks.Batch97.c8FourActionRecord79_covered, CertificateChecks.Batch97.c8FourActionRecord79_bounded, CertificateChecks.Batch97.c8FourActionRecord80_covered, CertificateChecks.Batch97.c8FourActionRecord80_bounded, CertificateChecks.Batch97.c8FourActionRecord81_covered, CertificateChecks.Batch97.c8FourActionRecord81_bounded, CertificateChecks.Batch97.c8FourActionRecord82_covered, CertificateChecks.Batch97.c8FourActionRecord82_bounded, CertificateChecks.Batch97.c8FourActionRecord83_covered, CertificateChecks.Batch97.c8FourActionRecord83_bounded, CertificateChecks.Batch97.c8FourActionRecord84_covered, CertificateChecks.Batch97.c8FourActionRecord84_bounded, CertificateChecks.Batch97.c8FourActionRecord85_covered, CertificateChecks.Batch97.c8FourActionRecord85_bounded, CertificateChecks.Batch97.c8FourActionRecord86_covered, CertificateChecks.Batch97.c8FourActionRecord86_bounded, CertificateChecks.Batch97.c8FourActionRecord87_covered, CertificateChecks.Batch97.c8FourActionRecord87_bounded, CertificateChecks.Batch97.c8FourActionRecord88_covered, CertificateChecks.Batch97.c8FourActionRecord88_bounded, CertificateChecks.Batch97.c8FourActionRecord89_covered, CertificateChecks.Batch97.c8FourActionRecord89_bounded, CertificateChecks.Batch97.c8FourActionRecord90_covered, CertificateChecks.Batch97.c8FourActionRecord90_bounded, CertificateChecks.Batch97.c8FourActionRecord91_covered, CertificateChecks.Batch97.c8FourActionRecord91_bounded, CertificateChecks.Batch97.c8FourActionRecord92_covered, CertificateChecks.Batch97.c8FourActionRecord92_bounded, CertificateChecks.Batch97.c8FourActionRecord93_covered, CertificateChecks.Batch97.c8FourActionRecord93_bounded, CertificateChecks.Batch97.c8FourActionRecord94_covered, CertificateChecks.Batch97.c8FourActionRecord94_bounded, CertificateChecks.Batch97.c8FourActionRecord95_covered, CertificateChecks.Batch97.c8FourActionRecord95_bounded, CertificateChecks.Batch97.c8FourActionRecord96_covered, CertificateChecks.Batch97.c8FourActionRecord96_bounded, CertificateChecks.Batch97.c8FourActionRecord97_covered, CertificateChecks.Batch97.c8FourActionRecord97_bounded, CertificateChecks.Batch97.c8FourActionRecord98_covered, CertificateChecks.Batch97.c8FourActionRecord98_bounded, CertificateChecks.Batch97.c8FourActionRecord99_covered, CertificateChecks.Batch97.c8FourActionRecord99_bounded, CertificateChecks.Batch97.c8FourActionRecord100_covered, CertificateChecks.Batch97.c8FourActionRecord100_bounded, CertificateChecks.Batch97.c8FourActionRecord101_covered, CertificateChecks.Batch97.c8FourActionRecord101_bounded, CertificateChecks.Batch97.c8FourActionRecord102_covered, CertificateChecks.Batch97.c8FourActionRecord102_bounded, CertificateChecks.Batch97.c8FourActionRecord103_covered, CertificateChecks.Batch97.c8FourActionRecord103_bounded, CertificateChecks.Batch97.c8FourActionRecord104_covered, CertificateChecks.Batch97.c8FourActionRecord104_bounded, CertificateChecks.Batch97.c8FourActionRecord105_covered, CertificateChecks.Batch97.c8FourActionRecord105_bounded, CertificateChecks.Batch97.c8FourActionRecord106_covered, CertificateChecks.Batch97.c8FourActionRecord106_bounded, CertificateChecks.Batch97.c8FourActionRecord107_covered, CertificateChecks.Batch97.c8FourActionRecord107_bounded, CertificateChecks.Batch97.c8FourActionRecord108_covered, CertificateChecks.Batch97.c8FourActionRecord108_bounded, CertificateChecks.Batch97.c8FourActionRecord109_covered, CertificateChecks.Batch97.c8FourActionRecord109_bounded, CertificateChecks.Batch97.c8FourActionRecord110_covered, CertificateChecks.Batch97.c8FourActionRecord110_bounded, CertificateChecks.Batch97.c8FourActionRecord111_covered, CertificateChecks.Batch97.c8FourActionRecord111_bounded, CertificateChecks.Batch97.c8FourActionRecord112_covered, CertificateChecks.Batch97.c8FourActionRecord112_bounded, CertificateChecks.Batch97.c8FourActionRecord113_covered, CertificateChecks.Batch97.c8FourActionRecord113_bounded, CertificateChecks.Batch97.c8FourActionRecord114_covered, CertificateChecks.Batch97.c8FourActionRecord114_bounded, CertificateChecks.Batch97.c8FourActionRecord115_covered, CertificateChecks.Batch97.c8FourActionRecord115_bounded, CertificateChecks.Batch97.c8FourActionRecord116_covered, CertificateChecks.Batch97.c8FourActionRecord116_bounded, CertificateChecks.Batch97.c8FourActionRecord117_covered, CertificateChecks.Batch97.c8FourActionRecord117_bounded, CertificateChecks.Batch97.c8FourActionRecord118_covered, CertificateChecks.Batch97.c8FourActionRecord118_bounded, CertificateChecks.Batch97.c8FourActionRecord119_covered, CertificateChecks.Batch97.c8FourActionRecord119_bounded, CertificateChecks.Batch97.c8FourActionRecord120_covered, CertificateChecks.Batch97.c8FourActionRecord120_bounded, CertificateChecks.Batch97.c8FourActionRecord121_covered, CertificateChecks.Batch97.c8FourActionRecord121_bounded, CertificateChecks.Batch97.c8FourActionRecord122_covered, CertificateChecks.Batch97.c8FourActionRecord122_bounded, CertificateChecks.Batch97.c8FourActionRecord123_covered, CertificateChecks.Batch97.c8FourActionRecord123_bounded, CertificateChecks.Batch97.c8FourActionRecord124_covered, CertificateChecks.Batch97.c8FourActionRecord124_bounded, CertificateChecks.Batch97.c8FourActionRecord125_covered, CertificateChecks.Batch97.c8FourActionRecord125_bounded, CertificateChecks.Batch97.c8FourActionRecord126_covered, CertificateChecks.Batch97.c8FourActionRecord126_bounded, CertificateChecks.Batch97.c8FourActionRecord127_covered, CertificateChecks.Batch97.c8FourActionRecord127_bounded⟩

end Certificates
