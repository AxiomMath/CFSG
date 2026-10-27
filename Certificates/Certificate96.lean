module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnessesCore

public section

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

namespace CertificateChecks.Batch96

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem c8FourActionRecord0_covered : c8FourActionCovered c8FourRecordData0 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord0_bounded : c8FourActionBounded c8FourRecordData0 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord1_covered : c8FourActionCovered c8FourRecordData1 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord1_bounded : c8FourActionBounded c8FourRecordData1 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord2_covered : c8FourActionCovered c8FourRecordData2 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord2_bounded : c8FourActionBounded c8FourRecordData2 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord3_covered : c8FourActionCovered c8FourRecordData3 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord3_bounded : c8FourActionBounded c8FourRecordData3 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord4_covered : c8FourActionCovered c8FourRecordData4 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord4_bounded : c8FourActionBounded c8FourRecordData4 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord5_covered : c8FourActionCovered c8FourRecordData5 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord5_bounded : c8FourActionBounded c8FourRecordData5 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord6_covered : c8FourActionCovered c8FourRecordData6 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord6_bounded : c8FourActionBounded c8FourRecordData6 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord7_covered : c8FourActionCovered c8FourRecordData7 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord7_bounded : c8FourActionBounded c8FourRecordData7 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord8_covered : c8FourActionCovered c8FourRecordData8 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord8_bounded : c8FourActionBounded c8FourRecordData8 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord9_covered : c8FourActionCovered c8FourRecordData9 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord9_bounded : c8FourActionBounded c8FourRecordData9 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord10_covered : c8FourActionCovered c8FourRecordData10 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord10_bounded : c8FourActionBounded c8FourRecordData10 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord11_covered : c8FourActionCovered c8FourRecordData11 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord11_bounded : c8FourActionBounded c8FourRecordData11 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord12_covered : c8FourActionCovered c8FourRecordData12 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord12_bounded : c8FourActionBounded c8FourRecordData12 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord13_covered : c8FourActionCovered c8FourRecordData13 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord13_bounded : c8FourActionBounded c8FourRecordData13 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord14_covered : c8FourActionCovered c8FourRecordData14 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord14_bounded : c8FourActionBounded c8FourRecordData14 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord15_covered : c8FourActionCovered c8FourRecordData15 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord15_bounded : c8FourActionBounded c8FourRecordData15 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord16_covered : c8FourActionCovered c8FourRecordData16 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord16_bounded : c8FourActionBounded c8FourRecordData16 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord17_covered : c8FourActionCovered c8FourRecordData17 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord17_bounded : c8FourActionBounded c8FourRecordData17 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord18_covered : c8FourActionCovered c8FourRecordData18 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord18_bounded : c8FourActionBounded c8FourRecordData18 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord19_covered : c8FourActionCovered c8FourRecordData19 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord19_bounded : c8FourActionBounded c8FourRecordData19 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord20_covered : c8FourActionCovered c8FourRecordData20 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord20_bounded : c8FourActionBounded c8FourRecordData20 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord21_covered : c8FourActionCovered c8FourRecordData21 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord21_bounded : c8FourActionBounded c8FourRecordData21 := by
  decide +kernel

private theorem c8FourActionRecord22_covered : c8FourActionCovered c8FourRecordData22 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord22_bounded : c8FourActionBounded c8FourRecordData22 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord23_covered : c8FourActionCovered c8FourRecordData23 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord23_bounded : c8FourActionBounded c8FourRecordData23 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord24_covered : c8FourActionCovered c8FourRecordData24 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord24_bounded : c8FourActionBounded c8FourRecordData24 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord25_covered : c8FourActionCovered c8FourRecordData25 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord25_bounded : c8FourActionBounded c8FourRecordData25 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord26_covered : c8FourActionCovered c8FourRecordData26 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord26_bounded : c8FourActionBounded c8FourRecordData26 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord27_covered : c8FourActionCovered c8FourRecordData27 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord27_bounded : c8FourActionBounded c8FourRecordData27 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord28_covered : c8FourActionCovered c8FourRecordData28 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord28_bounded : c8FourActionBounded c8FourRecordData28 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord29_covered : c8FourActionCovered c8FourRecordData29 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord29_bounded : c8FourActionBounded c8FourRecordData29 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord30_covered : c8FourActionCovered c8FourRecordData30 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord30_bounded : c8FourActionBounded c8FourRecordData30 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord31_covered : c8FourActionCovered c8FourRecordData31 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord31_bounded : c8FourActionBounded c8FourRecordData31 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord32_covered : c8FourActionCovered c8FourRecordData32 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord32_bounded : c8FourActionBounded c8FourRecordData32 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord33_covered : c8FourActionCovered c8FourRecordData33 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord33_bounded : c8FourActionBounded c8FourRecordData33 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord34_covered : c8FourActionCovered c8FourRecordData34 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord34_bounded : c8FourActionBounded c8FourRecordData34 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord35_covered : c8FourActionCovered c8FourRecordData35 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord35_bounded : c8FourActionBounded c8FourRecordData35 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord36_covered : c8FourActionCovered c8FourRecordData36 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord36_bounded : c8FourActionBounded c8FourRecordData36 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord37_covered : c8FourActionCovered c8FourRecordData37 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord37_bounded : c8FourActionBounded c8FourRecordData37 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord38_covered : c8FourActionCovered c8FourRecordData38 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord38_bounded : c8FourActionBounded c8FourRecordData38 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord39_covered : c8FourActionCovered c8FourRecordData39 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord39_bounded : c8FourActionBounded c8FourRecordData39 := by
  decide +kernel

private theorem c8FourActionRecord40_covered : c8FourActionCovered c8FourRecordData40 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord40_bounded : c8FourActionBounded c8FourRecordData40 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord41_covered : c8FourActionCovered c8FourRecordData41 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord41_bounded : c8FourActionBounded c8FourRecordData41 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord42_covered : c8FourActionCovered c8FourRecordData42 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord42_bounded : c8FourActionBounded c8FourRecordData42 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord43_covered : c8FourActionCovered c8FourRecordData43 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord43_bounded : c8FourActionBounded c8FourRecordData43 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord44_covered : c8FourActionCovered c8FourRecordData44 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord44_bounded : c8FourActionBounded c8FourRecordData44 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord45_covered : c8FourActionCovered c8FourRecordData45 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord45_bounded : c8FourActionBounded c8FourRecordData45 := by
  decide +kernel

private theorem c8FourActionRecord46_covered : c8FourActionCovered c8FourRecordData46 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord46_bounded : c8FourActionBounded c8FourRecordData46 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord47_covered : c8FourActionCovered c8FourRecordData47 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord47_bounded : c8FourActionBounded c8FourRecordData47 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord48_covered : c8FourActionCovered c8FourRecordData48 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord48_bounded : c8FourActionBounded c8FourRecordData48 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord49_covered : c8FourActionCovered c8FourRecordData49 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord49_bounded : c8FourActionBounded c8FourRecordData49 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord50_covered : c8FourActionCovered c8FourRecordData50 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord50_bounded : c8FourActionBounded c8FourRecordData50 := by
  decide +kernel

private theorem c8FourActionRecord51_covered : c8FourActionCovered c8FourRecordData51 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord51_bounded : c8FourActionBounded c8FourRecordData51 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord52_covered : c8FourActionCovered c8FourRecordData52 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord52_bounded : c8FourActionBounded c8FourRecordData52 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord53_covered : c8FourActionCovered c8FourRecordData53 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord53_bounded : c8FourActionBounded c8FourRecordData53 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord54_covered : c8FourActionCovered c8FourRecordData54 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord54_bounded : c8FourActionBounded c8FourRecordData54 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord55_covered : c8FourActionCovered c8FourRecordData55 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord55_bounded : c8FourActionBounded c8FourRecordData55 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord56_covered : c8FourActionCovered c8FourRecordData56 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord56_bounded : c8FourActionBounded c8FourRecordData56 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord57_covered : c8FourActionCovered c8FourRecordData57 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord57_bounded : c8FourActionBounded c8FourRecordData57 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord58_covered : c8FourActionCovered c8FourRecordData58 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord58_bounded : c8FourActionBounded c8FourRecordData58 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord59_covered : c8FourActionCovered c8FourRecordData59 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord59_bounded : c8FourActionBounded c8FourRecordData59 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord60_covered : c8FourActionCovered c8FourRecordData60 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord60_bounded : c8FourActionBounded c8FourRecordData60 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord61_covered : c8FourActionCovered c8FourRecordData61 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord61_bounded : c8FourActionBounded c8FourRecordData61 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord62_covered : c8FourActionCovered c8FourRecordData62 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord62_bounded : c8FourActionBounded c8FourRecordData62 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord63_covered : c8FourActionCovered c8FourRecordData63 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord63_bounded : c8FourActionBounded c8FourRecordData63 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionChunk0_covered (j : Fin 64) :
    c8FourActionCovered (c8FourRecordChunk0[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord0_covered
  · exact c8FourActionRecord1_covered
  · exact c8FourActionRecord2_covered
  · exact c8FourActionRecord3_covered
  · exact c8FourActionRecord4_covered
  · exact c8FourActionRecord5_covered
  · exact c8FourActionRecord6_covered
  · exact c8FourActionRecord7_covered
  · exact c8FourActionRecord8_covered
  · exact c8FourActionRecord9_covered
  · exact c8FourActionRecord10_covered
  · exact c8FourActionRecord11_covered
  · exact c8FourActionRecord12_covered
  · exact c8FourActionRecord13_covered
  · exact c8FourActionRecord14_covered
  · exact c8FourActionRecord15_covered
  · exact c8FourActionRecord16_covered
  · exact c8FourActionRecord17_covered
  · exact c8FourActionRecord18_covered
  · exact c8FourActionRecord19_covered
  · exact c8FourActionRecord20_covered
  · exact c8FourActionRecord21_covered
  · exact c8FourActionRecord22_covered
  · exact c8FourActionRecord23_covered
  · exact c8FourActionRecord24_covered
  · exact c8FourActionRecord25_covered
  · exact c8FourActionRecord26_covered
  · exact c8FourActionRecord27_covered
  · exact c8FourActionRecord28_covered
  · exact c8FourActionRecord29_covered
  · exact c8FourActionRecord30_covered
  · exact c8FourActionRecord31_covered
  · exact c8FourActionRecord32_covered
  · exact c8FourActionRecord33_covered
  · exact c8FourActionRecord34_covered
  · exact c8FourActionRecord35_covered
  · exact c8FourActionRecord36_covered
  · exact c8FourActionRecord37_covered
  · exact c8FourActionRecord38_covered
  · exact c8FourActionRecord39_covered
  · exact c8FourActionRecord40_covered
  · exact c8FourActionRecord41_covered
  · exact c8FourActionRecord42_covered
  · exact c8FourActionRecord43_covered
  · exact c8FourActionRecord44_covered
  · exact c8FourActionRecord45_covered
  · exact c8FourActionRecord46_covered
  · exact c8FourActionRecord47_covered
  · exact c8FourActionRecord48_covered
  · exact c8FourActionRecord49_covered
  · exact c8FourActionRecord50_covered
  · exact c8FourActionRecord51_covered
  · exact c8FourActionRecord52_covered
  · exact c8FourActionRecord53_covered
  · exact c8FourActionRecord54_covered
  · exact c8FourActionRecord55_covered
  · exact c8FourActionRecord56_covered
  · exact c8FourActionRecord57_covered
  · exact c8FourActionRecord58_covered
  · exact c8FourActionRecord59_covered
  · exact c8FourActionRecord60_covered
  · exact c8FourActionRecord61_covered
  · exact c8FourActionRecord62_covered
  · exact c8FourActionRecord63_covered

private theorem c8FourActionChunk0_bounded (j : Fin 64) :
    c8FourActionBounded (c8FourRecordChunk0[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord0_bounded
  · exact c8FourActionRecord1_bounded
  · exact c8FourActionRecord2_bounded
  · exact c8FourActionRecord3_bounded
  · exact c8FourActionRecord4_bounded
  · exact c8FourActionRecord5_bounded
  · exact c8FourActionRecord6_bounded
  · exact c8FourActionRecord7_bounded
  · exact c8FourActionRecord8_bounded
  · exact c8FourActionRecord9_bounded
  · exact c8FourActionRecord10_bounded
  · exact c8FourActionRecord11_bounded
  · exact c8FourActionRecord12_bounded
  · exact c8FourActionRecord13_bounded
  · exact c8FourActionRecord14_bounded
  · exact c8FourActionRecord15_bounded
  · exact c8FourActionRecord16_bounded
  · exact c8FourActionRecord17_bounded
  · exact c8FourActionRecord18_bounded
  · exact c8FourActionRecord19_bounded
  · exact c8FourActionRecord20_bounded
  · exact c8FourActionRecord21_bounded
  · exact c8FourActionRecord22_bounded
  · exact c8FourActionRecord23_bounded
  · exact c8FourActionRecord24_bounded
  · exact c8FourActionRecord25_bounded
  · exact c8FourActionRecord26_bounded
  · exact c8FourActionRecord27_bounded
  · exact c8FourActionRecord28_bounded
  · exact c8FourActionRecord29_bounded
  · exact c8FourActionRecord30_bounded
  · exact c8FourActionRecord31_bounded
  · exact c8FourActionRecord32_bounded
  · exact c8FourActionRecord33_bounded
  · exact c8FourActionRecord34_bounded
  · exact c8FourActionRecord35_bounded
  · exact c8FourActionRecord36_bounded
  · exact c8FourActionRecord37_bounded
  · exact c8FourActionRecord38_bounded
  · exact c8FourActionRecord39_bounded
  · exact c8FourActionRecord40_bounded
  · exact c8FourActionRecord41_bounded
  · exact c8FourActionRecord42_bounded
  · exact c8FourActionRecord43_bounded
  · exact c8FourActionRecord44_bounded
  · exact c8FourActionRecord45_bounded
  · exact c8FourActionRecord46_bounded
  · exact c8FourActionRecord47_bounded
  · exact c8FourActionRecord48_bounded
  · exact c8FourActionRecord49_bounded
  · exact c8FourActionRecord50_bounded
  · exact c8FourActionRecord51_bounded
  · exact c8FourActionRecord52_bounded
  · exact c8FourActionRecord53_bounded
  · exact c8FourActionRecord54_bounded
  · exact c8FourActionRecord55_bounded
  · exact c8FourActionRecord56_bounded
  · exact c8FourActionRecord57_bounded
  · exact c8FourActionRecord58_bounded
  · exact c8FourActionRecord59_bounded
  · exact c8FourActionRecord60_bounded
  · exact c8FourActionRecord61_bounded
  · exact c8FourActionRecord62_bounded
  · exact c8FourActionRecord63_bounded

end CertificateChecks.Batch96

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers in
theorem certificate96 : (c8FourActionCovered c8FourRecordData0)
    ∧ (c8FourActionBounded c8FourRecordData0)
    ∧ (c8FourActionCovered c8FourRecordData1)
    ∧ (c8FourActionBounded c8FourRecordData1)
    ∧ (c8FourActionCovered c8FourRecordData2)
    ∧ (c8FourActionBounded c8FourRecordData2)
    ∧ (c8FourActionCovered c8FourRecordData3)
    ∧ (c8FourActionBounded c8FourRecordData3)
    ∧ (c8FourActionCovered c8FourRecordData4)
    ∧ (c8FourActionBounded c8FourRecordData4)
    ∧ (c8FourActionCovered c8FourRecordData5)
    ∧ (c8FourActionBounded c8FourRecordData5)
    ∧ (c8FourActionCovered c8FourRecordData6)
    ∧ (c8FourActionBounded c8FourRecordData6)
    ∧ (c8FourActionCovered c8FourRecordData7)
    ∧ (c8FourActionBounded c8FourRecordData7)
    ∧ (c8FourActionCovered c8FourRecordData8)
    ∧ (c8FourActionBounded c8FourRecordData8)
    ∧ (c8FourActionCovered c8FourRecordData9)
    ∧ (c8FourActionBounded c8FourRecordData9)
    ∧ (c8FourActionCovered c8FourRecordData10)
    ∧ (c8FourActionBounded c8FourRecordData10)
    ∧ (c8FourActionCovered c8FourRecordData11)
    ∧ (c8FourActionBounded c8FourRecordData11)
    ∧ (c8FourActionCovered c8FourRecordData12)
    ∧ (c8FourActionBounded c8FourRecordData12)
    ∧ (c8FourActionCovered c8FourRecordData13)
    ∧ (c8FourActionBounded c8FourRecordData13)
    ∧ (c8FourActionCovered c8FourRecordData14)
    ∧ (c8FourActionBounded c8FourRecordData14)
    ∧ (c8FourActionCovered c8FourRecordData15)
    ∧ (c8FourActionBounded c8FourRecordData15)
    ∧ (c8FourActionCovered c8FourRecordData16)
    ∧ (c8FourActionBounded c8FourRecordData16)
    ∧ (c8FourActionCovered c8FourRecordData17)
    ∧ (c8FourActionBounded c8FourRecordData17)
    ∧ (c8FourActionCovered c8FourRecordData18)
    ∧ (c8FourActionBounded c8FourRecordData18)
    ∧ (c8FourActionCovered c8FourRecordData19)
    ∧ (c8FourActionBounded c8FourRecordData19)
    ∧ (c8FourActionCovered c8FourRecordData20)
    ∧ (c8FourActionBounded c8FourRecordData20)
    ∧ (c8FourActionCovered c8FourRecordData21)
    ∧ (c8FourActionBounded c8FourRecordData21)
    ∧ (c8FourActionCovered c8FourRecordData22)
    ∧ (c8FourActionBounded c8FourRecordData22)
    ∧ (c8FourActionCovered c8FourRecordData23)
    ∧ (c8FourActionBounded c8FourRecordData23)
    ∧ (c8FourActionCovered c8FourRecordData24)
    ∧ (c8FourActionBounded c8FourRecordData24)
    ∧ (c8FourActionCovered c8FourRecordData25)
    ∧ (c8FourActionBounded c8FourRecordData25)
    ∧ (c8FourActionCovered c8FourRecordData26)
    ∧ (c8FourActionBounded c8FourRecordData26)
    ∧ (c8FourActionCovered c8FourRecordData27)
    ∧ (c8FourActionBounded c8FourRecordData27)
    ∧ (c8FourActionCovered c8FourRecordData28)
    ∧ (c8FourActionBounded c8FourRecordData28)
    ∧ (c8FourActionCovered c8FourRecordData29)
    ∧ (c8FourActionBounded c8FourRecordData29)
    ∧ (c8FourActionCovered c8FourRecordData30)
    ∧ (c8FourActionBounded c8FourRecordData30)
    ∧ (c8FourActionCovered c8FourRecordData31)
    ∧ (c8FourActionBounded c8FourRecordData31)
    ∧ (c8FourActionCovered c8FourRecordData32)
    ∧ (c8FourActionBounded c8FourRecordData32)
    ∧ (c8FourActionCovered c8FourRecordData33)
    ∧ (c8FourActionBounded c8FourRecordData33)
    ∧ (c8FourActionCovered c8FourRecordData34)
    ∧ (c8FourActionBounded c8FourRecordData34)
    ∧ (c8FourActionCovered c8FourRecordData35)
    ∧ (c8FourActionBounded c8FourRecordData35)
    ∧ (c8FourActionCovered c8FourRecordData36)
    ∧ (c8FourActionBounded c8FourRecordData36)
    ∧ (c8FourActionCovered c8FourRecordData37)
    ∧ (c8FourActionBounded c8FourRecordData37)
    ∧ (c8FourActionCovered c8FourRecordData38)
    ∧ (c8FourActionBounded c8FourRecordData38)
    ∧ (c8FourActionCovered c8FourRecordData39)
    ∧ (c8FourActionBounded c8FourRecordData39)
    ∧ (c8FourActionCovered c8FourRecordData40)
    ∧ (c8FourActionBounded c8FourRecordData40)
    ∧ (c8FourActionCovered c8FourRecordData41)
    ∧ (c8FourActionBounded c8FourRecordData41)
    ∧ (c8FourActionCovered c8FourRecordData42)
    ∧ (c8FourActionBounded c8FourRecordData42)
    ∧ (c8FourActionCovered c8FourRecordData43)
    ∧ (c8FourActionBounded c8FourRecordData43)
    ∧ (c8FourActionCovered c8FourRecordData44)
    ∧ (c8FourActionBounded c8FourRecordData44)
    ∧ (c8FourActionCovered c8FourRecordData45)
    ∧ (c8FourActionBounded c8FourRecordData45)
    ∧ (c8FourActionCovered c8FourRecordData46)
    ∧ (c8FourActionBounded c8FourRecordData46)
    ∧ (c8FourActionCovered c8FourRecordData47)
    ∧ (c8FourActionBounded c8FourRecordData47)
    ∧ (c8FourActionCovered c8FourRecordData48)
    ∧ (c8FourActionBounded c8FourRecordData48)
    ∧ (c8FourActionCovered c8FourRecordData49)
    ∧ (c8FourActionBounded c8FourRecordData49)
    ∧ (c8FourActionCovered c8FourRecordData50)
    ∧ (c8FourActionBounded c8FourRecordData50)
    ∧ (c8FourActionCovered c8FourRecordData51)
    ∧ (c8FourActionBounded c8FourRecordData51)
    ∧ (c8FourActionCovered c8FourRecordData52)
    ∧ (c8FourActionBounded c8FourRecordData52)
    ∧ (c8FourActionCovered c8FourRecordData53)
    ∧ (c8FourActionBounded c8FourRecordData53)
    ∧ (c8FourActionCovered c8FourRecordData54)
    ∧ (c8FourActionBounded c8FourRecordData54)
    ∧ (c8FourActionCovered c8FourRecordData55)
    ∧ (c8FourActionBounded c8FourRecordData55)
    ∧ (c8FourActionCovered c8FourRecordData56)
    ∧ (c8FourActionBounded c8FourRecordData56)
    ∧ (c8FourActionCovered c8FourRecordData57)
    ∧ (c8FourActionBounded c8FourRecordData57)
    ∧ (c8FourActionCovered c8FourRecordData58)
    ∧ (c8FourActionBounded c8FourRecordData58)
    ∧ (c8FourActionCovered c8FourRecordData59)
    ∧ (c8FourActionBounded c8FourRecordData59)
    ∧ (c8FourActionCovered c8FourRecordData60)
    ∧ (c8FourActionBounded c8FourRecordData60)
    ∧ (c8FourActionCovered c8FourRecordData61)
    ∧ (c8FourActionBounded c8FourRecordData61)
    ∧ (c8FourActionCovered c8FourRecordData62)
    ∧ (c8FourActionBounded c8FourRecordData62)
    ∧ (c8FourActionCovered c8FourRecordData63)
    ∧ (c8FourActionBounded c8FourRecordData63) := by
  exact ⟨CertificateChecks.Batch96.c8FourActionRecord0_covered, CertificateChecks.Batch96.c8FourActionRecord0_bounded, CertificateChecks.Batch96.c8FourActionRecord1_covered, CertificateChecks.Batch96.c8FourActionRecord1_bounded, CertificateChecks.Batch96.c8FourActionRecord2_covered, CertificateChecks.Batch96.c8FourActionRecord2_bounded, CertificateChecks.Batch96.c8FourActionRecord3_covered, CertificateChecks.Batch96.c8FourActionRecord3_bounded, CertificateChecks.Batch96.c8FourActionRecord4_covered, CertificateChecks.Batch96.c8FourActionRecord4_bounded, CertificateChecks.Batch96.c8FourActionRecord5_covered, CertificateChecks.Batch96.c8FourActionRecord5_bounded, CertificateChecks.Batch96.c8FourActionRecord6_covered, CertificateChecks.Batch96.c8FourActionRecord6_bounded, CertificateChecks.Batch96.c8FourActionRecord7_covered, CertificateChecks.Batch96.c8FourActionRecord7_bounded, CertificateChecks.Batch96.c8FourActionRecord8_covered, CertificateChecks.Batch96.c8FourActionRecord8_bounded, CertificateChecks.Batch96.c8FourActionRecord9_covered, CertificateChecks.Batch96.c8FourActionRecord9_bounded, CertificateChecks.Batch96.c8FourActionRecord10_covered, CertificateChecks.Batch96.c8FourActionRecord10_bounded, CertificateChecks.Batch96.c8FourActionRecord11_covered, CertificateChecks.Batch96.c8FourActionRecord11_bounded, CertificateChecks.Batch96.c8FourActionRecord12_covered, CertificateChecks.Batch96.c8FourActionRecord12_bounded, CertificateChecks.Batch96.c8FourActionRecord13_covered, CertificateChecks.Batch96.c8FourActionRecord13_bounded, CertificateChecks.Batch96.c8FourActionRecord14_covered, CertificateChecks.Batch96.c8FourActionRecord14_bounded, CertificateChecks.Batch96.c8FourActionRecord15_covered, CertificateChecks.Batch96.c8FourActionRecord15_bounded, CertificateChecks.Batch96.c8FourActionRecord16_covered, CertificateChecks.Batch96.c8FourActionRecord16_bounded, CertificateChecks.Batch96.c8FourActionRecord17_covered, CertificateChecks.Batch96.c8FourActionRecord17_bounded, CertificateChecks.Batch96.c8FourActionRecord18_covered, CertificateChecks.Batch96.c8FourActionRecord18_bounded, CertificateChecks.Batch96.c8FourActionRecord19_covered, CertificateChecks.Batch96.c8FourActionRecord19_bounded, CertificateChecks.Batch96.c8FourActionRecord20_covered, CertificateChecks.Batch96.c8FourActionRecord20_bounded, CertificateChecks.Batch96.c8FourActionRecord21_covered, CertificateChecks.Batch96.c8FourActionRecord21_bounded, CertificateChecks.Batch96.c8FourActionRecord22_covered, CertificateChecks.Batch96.c8FourActionRecord22_bounded, CertificateChecks.Batch96.c8FourActionRecord23_covered, CertificateChecks.Batch96.c8FourActionRecord23_bounded, CertificateChecks.Batch96.c8FourActionRecord24_covered, CertificateChecks.Batch96.c8FourActionRecord24_bounded, CertificateChecks.Batch96.c8FourActionRecord25_covered, CertificateChecks.Batch96.c8FourActionRecord25_bounded, CertificateChecks.Batch96.c8FourActionRecord26_covered, CertificateChecks.Batch96.c8FourActionRecord26_bounded, CertificateChecks.Batch96.c8FourActionRecord27_covered, CertificateChecks.Batch96.c8FourActionRecord27_bounded, CertificateChecks.Batch96.c8FourActionRecord28_covered, CertificateChecks.Batch96.c8FourActionRecord28_bounded, CertificateChecks.Batch96.c8FourActionRecord29_covered, CertificateChecks.Batch96.c8FourActionRecord29_bounded, CertificateChecks.Batch96.c8FourActionRecord30_covered, CertificateChecks.Batch96.c8FourActionRecord30_bounded, CertificateChecks.Batch96.c8FourActionRecord31_covered, CertificateChecks.Batch96.c8FourActionRecord31_bounded, CertificateChecks.Batch96.c8FourActionRecord32_covered, CertificateChecks.Batch96.c8FourActionRecord32_bounded, CertificateChecks.Batch96.c8FourActionRecord33_covered, CertificateChecks.Batch96.c8FourActionRecord33_bounded, CertificateChecks.Batch96.c8FourActionRecord34_covered, CertificateChecks.Batch96.c8FourActionRecord34_bounded, CertificateChecks.Batch96.c8FourActionRecord35_covered, CertificateChecks.Batch96.c8FourActionRecord35_bounded, CertificateChecks.Batch96.c8FourActionRecord36_covered, CertificateChecks.Batch96.c8FourActionRecord36_bounded, CertificateChecks.Batch96.c8FourActionRecord37_covered, CertificateChecks.Batch96.c8FourActionRecord37_bounded, CertificateChecks.Batch96.c8FourActionRecord38_covered, CertificateChecks.Batch96.c8FourActionRecord38_bounded, CertificateChecks.Batch96.c8FourActionRecord39_covered, CertificateChecks.Batch96.c8FourActionRecord39_bounded, CertificateChecks.Batch96.c8FourActionRecord40_covered, CertificateChecks.Batch96.c8FourActionRecord40_bounded, CertificateChecks.Batch96.c8FourActionRecord41_covered, CertificateChecks.Batch96.c8FourActionRecord41_bounded, CertificateChecks.Batch96.c8FourActionRecord42_covered, CertificateChecks.Batch96.c8FourActionRecord42_bounded, CertificateChecks.Batch96.c8FourActionRecord43_covered, CertificateChecks.Batch96.c8FourActionRecord43_bounded, CertificateChecks.Batch96.c8FourActionRecord44_covered, CertificateChecks.Batch96.c8FourActionRecord44_bounded, CertificateChecks.Batch96.c8FourActionRecord45_covered, CertificateChecks.Batch96.c8FourActionRecord45_bounded, CertificateChecks.Batch96.c8FourActionRecord46_covered, CertificateChecks.Batch96.c8FourActionRecord46_bounded, CertificateChecks.Batch96.c8FourActionRecord47_covered, CertificateChecks.Batch96.c8FourActionRecord47_bounded, CertificateChecks.Batch96.c8FourActionRecord48_covered, CertificateChecks.Batch96.c8FourActionRecord48_bounded, CertificateChecks.Batch96.c8FourActionRecord49_covered, CertificateChecks.Batch96.c8FourActionRecord49_bounded, CertificateChecks.Batch96.c8FourActionRecord50_covered, CertificateChecks.Batch96.c8FourActionRecord50_bounded, CertificateChecks.Batch96.c8FourActionRecord51_covered, CertificateChecks.Batch96.c8FourActionRecord51_bounded, CertificateChecks.Batch96.c8FourActionRecord52_covered, CertificateChecks.Batch96.c8FourActionRecord52_bounded, CertificateChecks.Batch96.c8FourActionRecord53_covered, CertificateChecks.Batch96.c8FourActionRecord53_bounded, CertificateChecks.Batch96.c8FourActionRecord54_covered, CertificateChecks.Batch96.c8FourActionRecord54_bounded, CertificateChecks.Batch96.c8FourActionRecord55_covered, CertificateChecks.Batch96.c8FourActionRecord55_bounded, CertificateChecks.Batch96.c8FourActionRecord56_covered, CertificateChecks.Batch96.c8FourActionRecord56_bounded, CertificateChecks.Batch96.c8FourActionRecord57_covered, CertificateChecks.Batch96.c8FourActionRecord57_bounded, CertificateChecks.Batch96.c8FourActionRecord58_covered, CertificateChecks.Batch96.c8FourActionRecord58_bounded, CertificateChecks.Batch96.c8FourActionRecord59_covered, CertificateChecks.Batch96.c8FourActionRecord59_bounded, CertificateChecks.Batch96.c8FourActionRecord60_covered, CertificateChecks.Batch96.c8FourActionRecord60_bounded, CertificateChecks.Batch96.c8FourActionRecord61_covered, CertificateChecks.Batch96.c8FourActionRecord61_bounded, CertificateChecks.Batch96.c8FourActionRecord62_covered, CertificateChecks.Batch96.c8FourActionRecord62_bounded, CertificateChecks.Batch96.c8FourActionRecord63_covered, CertificateChecks.Batch96.c8FourActionRecord63_bounded⟩

end Certificates
