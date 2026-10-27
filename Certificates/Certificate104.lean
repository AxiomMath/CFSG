module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnessesCore

public section

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

namespace CertificateChecks.Batch104

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem c8FourActionRecord256_covered : c8FourActionCovered c8FourRecordData256 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord256_bounded : c8FourActionBounded c8FourRecordData256 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord257_covered : c8FourActionCovered c8FourRecordData257 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord257_bounded : c8FourActionBounded c8FourRecordData257 := by
  decide +kernel

private theorem c8FourActionRecord258_covered : c8FourActionCovered c8FourRecordData258 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord258_bounded : c8FourActionBounded c8FourRecordData258 := by
  decide +kernel

private theorem c8FourActionRecord259_covered : c8FourActionCovered c8FourRecordData259 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord259_bounded : c8FourActionBounded c8FourRecordData259 := by
  decide +kernel

private theorem c8FourActionRecord260_covered : c8FourActionCovered c8FourRecordData260 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord260_bounded : c8FourActionBounded c8FourRecordData260 := by
  decide +kernel

private theorem c8FourActionRecord261_covered : c8FourActionCovered c8FourRecordData261 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord261_bounded : c8FourActionBounded c8FourRecordData261 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord262_covered : c8FourActionCovered c8FourRecordData262 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord262_bounded : c8FourActionBounded c8FourRecordData262 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord263_covered : c8FourActionCovered c8FourRecordData263 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord263_bounded : c8FourActionBounded c8FourRecordData263 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord264_covered : c8FourActionCovered c8FourRecordData264 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord264_bounded : c8FourActionBounded c8FourRecordData264 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord265_covered : c8FourActionCovered c8FourRecordData265 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨24, ?_⟩
  decide +kernel

private theorem c8FourActionRecord265_bounded : c8FourActionBounded c8FourRecordData265 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord266_covered : c8FourActionCovered c8FourRecordData266 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨12, ?_⟩
  decide +kernel

private theorem c8FourActionRecord266_bounded : c8FourActionBounded c8FourRecordData266 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord267_covered : c8FourActionCovered c8FourRecordData267 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨14, ?_⟩
  decide +kernel

private theorem c8FourActionRecord267_bounded : c8FourActionBounded c8FourRecordData267 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord268_covered : c8FourActionCovered c8FourRecordData268 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨24, ?_⟩
  decide +kernel

private theorem c8FourActionRecord268_bounded : c8FourActionBounded c8FourRecordData268 := by
  decide +kernel

private theorem c8FourActionRecord269_covered : c8FourActionCovered c8FourRecordData269 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord269_bounded : c8FourActionBounded c8FourRecordData269 := by
  decide +kernel

private theorem c8FourActionRecord270_covered : c8FourActionCovered c8FourRecordData270 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨49, ?_⟩
  decide +kernel

private theorem c8FourActionRecord270_bounded : c8FourActionBounded c8FourRecordData270 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord271_covered : c8FourActionCovered c8FourRecordData271 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord271_bounded : c8FourActionBounded c8FourRecordData271 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord272_covered : c8FourActionCovered c8FourRecordData272 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord272_bounded : c8FourActionBounded c8FourRecordData272 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord273_covered : c8FourActionCovered c8FourRecordData273 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨6, ?_⟩
  decide +kernel

private theorem c8FourActionRecord273_bounded : c8FourActionBounded c8FourRecordData273 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord274_covered : c8FourActionCovered c8FourRecordData274 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨6, ?_⟩
  decide +kernel

private theorem c8FourActionRecord274_bounded : c8FourActionBounded c8FourRecordData274 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord275_covered : c8FourActionCovered c8FourRecordData275 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨10, ?_⟩
  decide +kernel

private theorem c8FourActionRecord275_bounded : c8FourActionBounded c8FourRecordData275 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord276_covered : c8FourActionCovered c8FourRecordData276 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord276_bounded : c8FourActionBounded c8FourRecordData276 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord277_covered : c8FourActionCovered c8FourRecordData277 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord277_bounded : c8FourActionBounded c8FourRecordData277 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord278_covered : c8FourActionCovered c8FourRecordData278 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord278_bounded : c8FourActionBounded c8FourRecordData278 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord279_covered : c8FourActionCovered c8FourRecordData279 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord279_bounded : c8FourActionBounded c8FourRecordData279 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord280_covered : c8FourActionCovered c8FourRecordData280 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord280_bounded : c8FourActionBounded c8FourRecordData280 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord281_covered : c8FourActionCovered c8FourRecordData281 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord281_bounded : c8FourActionBounded c8FourRecordData281 := by
  decide +kernel

private theorem c8FourActionRecord282_covered : c8FourActionCovered c8FourRecordData282 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨12, ?_⟩
  decide +kernel

private theorem c8FourActionRecord282_bounded : c8FourActionBounded c8FourRecordData282 := by
  decide +kernel

private theorem c8FourActionRecord283_covered : c8FourActionCovered c8FourRecordData283 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord283_bounded : c8FourActionBounded c8FourRecordData283 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord284_covered : c8FourActionCovered c8FourRecordData284 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord284_bounded : c8FourActionBounded c8FourRecordData284 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord285_covered : c8FourActionCovered c8FourRecordData285 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord285_bounded : c8FourActionBounded c8FourRecordData285 := by
  decide +kernel

private theorem c8FourActionRecord286_covered : c8FourActionCovered c8FourRecordData286 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord286_bounded : c8FourActionBounded c8FourRecordData286 := by
  decide +kernel

private theorem c8FourActionRecord287_covered : c8FourActionCovered c8FourRecordData287 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨6, ?_⟩
  decide +kernel

private theorem c8FourActionRecord287_bounded : c8FourActionBounded c8FourRecordData287 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord288_covered : c8FourActionCovered c8FourRecordData288 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨6, ?_⟩
  decide +kernel

private theorem c8FourActionRecord288_bounded : c8FourActionBounded c8FourRecordData288 := by
  decide +kernel

private theorem c8FourActionRecord289_covered : c8FourActionCovered c8FourRecordData289 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord289_bounded : c8FourActionBounded c8FourRecordData289 := by
  decide +kernel

private theorem c8FourActionRecord290_covered : c8FourActionCovered c8FourRecordData290 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord290_bounded : c8FourActionBounded c8FourRecordData290 := by
  decide +kernel

private theorem c8FourActionRecord291_covered : c8FourActionCovered c8FourRecordData291 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord291_bounded : c8FourActionBounded c8FourRecordData291 := by
  decide +kernel

private theorem c8FourActionRecord292_covered : c8FourActionCovered c8FourRecordData292 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨7, ?_⟩
  decide +kernel

private theorem c8FourActionRecord292_bounded : c8FourActionBounded c8FourRecordData292 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord293_covered : c8FourActionCovered c8FourRecordData293 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord293_bounded : c8FourActionBounded c8FourRecordData293 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord294_covered : c8FourActionCovered c8FourRecordData294 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨7, ?_⟩
  decide +kernel

private theorem c8FourActionRecord294_bounded : c8FourActionBounded c8FourRecordData294 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord295_covered : c8FourActionCovered c8FourRecordData295 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord295_bounded : c8FourActionBounded c8FourRecordData295 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord296_covered : c8FourActionCovered c8FourRecordData296 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨7, ?_⟩
  decide +kernel

private theorem c8FourActionRecord296_bounded : c8FourActionBounded c8FourRecordData296 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord297_covered : c8FourActionCovered c8FourRecordData297 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨10, ?_⟩
  decide +kernel

private theorem c8FourActionRecord297_bounded : c8FourActionBounded c8FourRecordData297 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord298_covered : c8FourActionCovered c8FourRecordData298 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord298_bounded : c8FourActionBounded c8FourRecordData298 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord299_covered : c8FourActionCovered c8FourRecordData299 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord299_bounded : c8FourActionBounded c8FourRecordData299 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord300_covered : c8FourActionCovered c8FourRecordData300 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨8, ?_⟩
  decide +kernel

private theorem c8FourActionRecord300_bounded : c8FourActionBounded c8FourRecordData300 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord301_covered : c8FourActionCovered c8FourRecordData301 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord301_bounded : c8FourActionBounded c8FourRecordData301 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord302_covered : c8FourActionCovered c8FourRecordData302 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨8, ?_⟩
  decide +kernel

private theorem c8FourActionRecord302_bounded : c8FourActionBounded c8FourRecordData302 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord303_covered : c8FourActionCovered c8FourRecordData303 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨7, ?_⟩
  decide +kernel

private theorem c8FourActionRecord303_bounded : c8FourActionBounded c8FourRecordData303 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord304_covered : c8FourActionCovered c8FourRecordData304 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨7, ?_⟩
  decide +kernel

private theorem c8FourActionRecord304_bounded : c8FourActionBounded c8FourRecordData304 := by
  decide +kernel

private theorem c8FourActionRecord305_covered : c8FourActionCovered c8FourRecordData305 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord305_bounded : c8FourActionBounded c8FourRecordData305 := by
  decide +kernel

private theorem c8FourActionRecord306_covered : c8FourActionCovered c8FourRecordData306 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord306_bounded : c8FourActionBounded c8FourRecordData306 := by
  decide +kernel

private theorem c8FourActionRecord307_covered : c8FourActionCovered c8FourRecordData307 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord307_bounded : c8FourActionBounded c8FourRecordData307 := by
  decide +kernel

private theorem c8FourActionRecord308_covered : c8FourActionCovered c8FourRecordData308 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨8, ?_⟩
  decide +kernel

private theorem c8FourActionRecord308_bounded : c8FourActionBounded c8FourRecordData308 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord309_covered : c8FourActionCovered c8FourRecordData309 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord309_bounded : c8FourActionBounded c8FourRecordData309 := by
  decide +kernel

private theorem c8FourActionRecord310_covered : c8FourActionCovered c8FourRecordData310 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨14, ?_⟩
  decide +kernel

private theorem c8FourActionRecord310_bounded : c8FourActionBounded c8FourRecordData310 := by
  decide +kernel

private theorem c8FourActionRecord311_covered : c8FourActionCovered c8FourRecordData311 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord311_bounded : c8FourActionBounded c8FourRecordData311 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord312_covered : c8FourActionCovered c8FourRecordData312 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord312_bounded : c8FourActionBounded c8FourRecordData312 := by
  decide +kernel

private theorem c8FourActionRecord313_covered : c8FourActionCovered c8FourRecordData313 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord313_bounded : c8FourActionBounded c8FourRecordData313 := by
  decide +kernel

private theorem c8FourActionRecord314_covered : c8FourActionCovered c8FourRecordData314 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨8, ?_⟩
  decide +kernel

private theorem c8FourActionRecord314_bounded : c8FourActionBounded c8FourRecordData314 := by
  decide +kernel

private theorem c8FourActionRecord315_covered : c8FourActionCovered c8FourRecordData315 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord315_bounded : c8FourActionBounded c8FourRecordData315 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord316_covered : c8FourActionCovered c8FourRecordData316 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord316_bounded : c8FourActionBounded c8FourRecordData316 := by
  decide +kernel

private theorem c8FourActionRecord317_covered : c8FourActionCovered c8FourRecordData317 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨30, ?_⟩
  decide +kernel

private theorem c8FourActionRecord317_bounded : c8FourActionBounded c8FourRecordData317 := by
  decide +kernel

private theorem c8FourActionRecord318_covered : c8FourActionCovered c8FourRecordData318 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨10, ?_⟩
  decide +kernel

private theorem c8FourActionRecord318_bounded : c8FourActionBounded c8FourRecordData318 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord319_covered : c8FourActionCovered c8FourRecordData319 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord319_bounded : c8FourActionBounded c8FourRecordData319 := by
  decide +kernel

private theorem c8FourActionChunk4_covered (j : Fin 64) :
    c8FourActionCovered (c8FourRecordChunk4[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord256_covered
  · exact c8FourActionRecord257_covered
  · exact c8FourActionRecord258_covered
  · exact c8FourActionRecord259_covered
  · exact c8FourActionRecord260_covered
  · exact c8FourActionRecord261_covered
  · exact c8FourActionRecord262_covered
  · exact c8FourActionRecord263_covered
  · exact c8FourActionRecord264_covered
  · exact c8FourActionRecord265_covered
  · exact c8FourActionRecord266_covered
  · exact c8FourActionRecord267_covered
  · exact c8FourActionRecord268_covered
  · exact c8FourActionRecord269_covered
  · exact c8FourActionRecord270_covered
  · exact c8FourActionRecord271_covered
  · exact c8FourActionRecord272_covered
  · exact c8FourActionRecord273_covered
  · exact c8FourActionRecord274_covered
  · exact c8FourActionRecord275_covered
  · exact c8FourActionRecord276_covered
  · exact c8FourActionRecord277_covered
  · exact c8FourActionRecord278_covered
  · exact c8FourActionRecord279_covered
  · exact c8FourActionRecord280_covered
  · exact c8FourActionRecord281_covered
  · exact c8FourActionRecord282_covered
  · exact c8FourActionRecord283_covered
  · exact c8FourActionRecord284_covered
  · exact c8FourActionRecord285_covered
  · exact c8FourActionRecord286_covered
  · exact c8FourActionRecord287_covered
  · exact c8FourActionRecord288_covered
  · exact c8FourActionRecord289_covered
  · exact c8FourActionRecord290_covered
  · exact c8FourActionRecord291_covered
  · exact c8FourActionRecord292_covered
  · exact c8FourActionRecord293_covered
  · exact c8FourActionRecord294_covered
  · exact c8FourActionRecord295_covered
  · exact c8FourActionRecord296_covered
  · exact c8FourActionRecord297_covered
  · exact c8FourActionRecord298_covered
  · exact c8FourActionRecord299_covered
  · exact c8FourActionRecord300_covered
  · exact c8FourActionRecord301_covered
  · exact c8FourActionRecord302_covered
  · exact c8FourActionRecord303_covered
  · exact c8FourActionRecord304_covered
  · exact c8FourActionRecord305_covered
  · exact c8FourActionRecord306_covered
  · exact c8FourActionRecord307_covered
  · exact c8FourActionRecord308_covered
  · exact c8FourActionRecord309_covered
  · exact c8FourActionRecord310_covered
  · exact c8FourActionRecord311_covered
  · exact c8FourActionRecord312_covered
  · exact c8FourActionRecord313_covered
  · exact c8FourActionRecord314_covered
  · exact c8FourActionRecord315_covered
  · exact c8FourActionRecord316_covered
  · exact c8FourActionRecord317_covered
  · exact c8FourActionRecord318_covered
  · exact c8FourActionRecord319_covered

private theorem c8FourActionChunk4_bounded (j : Fin 64) :
    c8FourActionBounded (c8FourRecordChunk4[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord256_bounded
  · exact c8FourActionRecord257_bounded
  · exact c8FourActionRecord258_bounded
  · exact c8FourActionRecord259_bounded
  · exact c8FourActionRecord260_bounded
  · exact c8FourActionRecord261_bounded
  · exact c8FourActionRecord262_bounded
  · exact c8FourActionRecord263_bounded
  · exact c8FourActionRecord264_bounded
  · exact c8FourActionRecord265_bounded
  · exact c8FourActionRecord266_bounded
  · exact c8FourActionRecord267_bounded
  · exact c8FourActionRecord268_bounded
  · exact c8FourActionRecord269_bounded
  · exact c8FourActionRecord270_bounded
  · exact c8FourActionRecord271_bounded
  · exact c8FourActionRecord272_bounded
  · exact c8FourActionRecord273_bounded
  · exact c8FourActionRecord274_bounded
  · exact c8FourActionRecord275_bounded
  · exact c8FourActionRecord276_bounded
  · exact c8FourActionRecord277_bounded
  · exact c8FourActionRecord278_bounded
  · exact c8FourActionRecord279_bounded
  · exact c8FourActionRecord280_bounded
  · exact c8FourActionRecord281_bounded
  · exact c8FourActionRecord282_bounded
  · exact c8FourActionRecord283_bounded
  · exact c8FourActionRecord284_bounded
  · exact c8FourActionRecord285_bounded
  · exact c8FourActionRecord286_bounded
  · exact c8FourActionRecord287_bounded
  · exact c8FourActionRecord288_bounded
  · exact c8FourActionRecord289_bounded
  · exact c8FourActionRecord290_bounded
  · exact c8FourActionRecord291_bounded
  · exact c8FourActionRecord292_bounded
  · exact c8FourActionRecord293_bounded
  · exact c8FourActionRecord294_bounded
  · exact c8FourActionRecord295_bounded
  · exact c8FourActionRecord296_bounded
  · exact c8FourActionRecord297_bounded
  · exact c8FourActionRecord298_bounded
  · exact c8FourActionRecord299_bounded
  · exact c8FourActionRecord300_bounded
  · exact c8FourActionRecord301_bounded
  · exact c8FourActionRecord302_bounded
  · exact c8FourActionRecord303_bounded
  · exact c8FourActionRecord304_bounded
  · exact c8FourActionRecord305_bounded
  · exact c8FourActionRecord306_bounded
  · exact c8FourActionRecord307_bounded
  · exact c8FourActionRecord308_bounded
  · exact c8FourActionRecord309_bounded
  · exact c8FourActionRecord310_bounded
  · exact c8FourActionRecord311_bounded
  · exact c8FourActionRecord312_bounded
  · exact c8FourActionRecord313_bounded
  · exact c8FourActionRecord314_bounded
  · exact c8FourActionRecord315_bounded
  · exact c8FourActionRecord316_bounded
  · exact c8FourActionRecord317_bounded
  · exact c8FourActionRecord318_bounded
  · exact c8FourActionRecord319_bounded

end CertificateChecks.Batch104

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers in
theorem certificate104 : (c8FourActionCovered c8FourRecordData256)
    ∧ (c8FourActionBounded c8FourRecordData256)
    ∧ (c8FourActionCovered c8FourRecordData257)
    ∧ (c8FourActionBounded c8FourRecordData257)
    ∧ (c8FourActionCovered c8FourRecordData258)
    ∧ (c8FourActionBounded c8FourRecordData258)
    ∧ (c8FourActionCovered c8FourRecordData259)
    ∧ (c8FourActionBounded c8FourRecordData259)
    ∧ (c8FourActionCovered c8FourRecordData260)
    ∧ (c8FourActionBounded c8FourRecordData260)
    ∧ (c8FourActionCovered c8FourRecordData261)
    ∧ (c8FourActionBounded c8FourRecordData261)
    ∧ (c8FourActionCovered c8FourRecordData262)
    ∧ (c8FourActionBounded c8FourRecordData262)
    ∧ (c8FourActionCovered c8FourRecordData263)
    ∧ (c8FourActionBounded c8FourRecordData263)
    ∧ (c8FourActionCovered c8FourRecordData264)
    ∧ (c8FourActionBounded c8FourRecordData264)
    ∧ (c8FourActionCovered c8FourRecordData265)
    ∧ (c8FourActionBounded c8FourRecordData265)
    ∧ (c8FourActionCovered c8FourRecordData266)
    ∧ (c8FourActionBounded c8FourRecordData266)
    ∧ (c8FourActionCovered c8FourRecordData267)
    ∧ (c8FourActionBounded c8FourRecordData267)
    ∧ (c8FourActionCovered c8FourRecordData268)
    ∧ (c8FourActionBounded c8FourRecordData268)
    ∧ (c8FourActionCovered c8FourRecordData269)
    ∧ (c8FourActionBounded c8FourRecordData269)
    ∧ (c8FourActionCovered c8FourRecordData270)
    ∧ (c8FourActionBounded c8FourRecordData270)
    ∧ (c8FourActionCovered c8FourRecordData271)
    ∧ (c8FourActionBounded c8FourRecordData271)
    ∧ (c8FourActionCovered c8FourRecordData272)
    ∧ (c8FourActionBounded c8FourRecordData272)
    ∧ (c8FourActionCovered c8FourRecordData273)
    ∧ (c8FourActionBounded c8FourRecordData273)
    ∧ (c8FourActionCovered c8FourRecordData274)
    ∧ (c8FourActionBounded c8FourRecordData274)
    ∧ (c8FourActionCovered c8FourRecordData275)
    ∧ (c8FourActionBounded c8FourRecordData275)
    ∧ (c8FourActionCovered c8FourRecordData276)
    ∧ (c8FourActionBounded c8FourRecordData276)
    ∧ (c8FourActionCovered c8FourRecordData277)
    ∧ (c8FourActionBounded c8FourRecordData277)
    ∧ (c8FourActionCovered c8FourRecordData278)
    ∧ (c8FourActionBounded c8FourRecordData278)
    ∧ (c8FourActionCovered c8FourRecordData279)
    ∧ (c8FourActionBounded c8FourRecordData279)
    ∧ (c8FourActionCovered c8FourRecordData280)
    ∧ (c8FourActionBounded c8FourRecordData280)
    ∧ (c8FourActionCovered c8FourRecordData281)
    ∧ (c8FourActionBounded c8FourRecordData281)
    ∧ (c8FourActionCovered c8FourRecordData282)
    ∧ (c8FourActionBounded c8FourRecordData282)
    ∧ (c8FourActionCovered c8FourRecordData283)
    ∧ (c8FourActionBounded c8FourRecordData283)
    ∧ (c8FourActionCovered c8FourRecordData284)
    ∧ (c8FourActionBounded c8FourRecordData284)
    ∧ (c8FourActionCovered c8FourRecordData285)
    ∧ (c8FourActionBounded c8FourRecordData285)
    ∧ (c8FourActionCovered c8FourRecordData286)
    ∧ (c8FourActionBounded c8FourRecordData286)
    ∧ (c8FourActionCovered c8FourRecordData287)
    ∧ (c8FourActionBounded c8FourRecordData287)
    ∧ (c8FourActionCovered c8FourRecordData288)
    ∧ (c8FourActionBounded c8FourRecordData288)
    ∧ (c8FourActionCovered c8FourRecordData289)
    ∧ (c8FourActionBounded c8FourRecordData289)
    ∧ (c8FourActionCovered c8FourRecordData290)
    ∧ (c8FourActionBounded c8FourRecordData290)
    ∧ (c8FourActionCovered c8FourRecordData291)
    ∧ (c8FourActionBounded c8FourRecordData291)
    ∧ (c8FourActionCovered c8FourRecordData292)
    ∧ (c8FourActionBounded c8FourRecordData292)
    ∧ (c8FourActionCovered c8FourRecordData293)
    ∧ (c8FourActionBounded c8FourRecordData293)
    ∧ (c8FourActionCovered c8FourRecordData294)
    ∧ (c8FourActionBounded c8FourRecordData294)
    ∧ (c8FourActionCovered c8FourRecordData295)
    ∧ (c8FourActionBounded c8FourRecordData295)
    ∧ (c8FourActionCovered c8FourRecordData296)
    ∧ (c8FourActionBounded c8FourRecordData296)
    ∧ (c8FourActionCovered c8FourRecordData297)
    ∧ (c8FourActionBounded c8FourRecordData297)
    ∧ (c8FourActionCovered c8FourRecordData298)
    ∧ (c8FourActionBounded c8FourRecordData298)
    ∧ (c8FourActionCovered c8FourRecordData299)
    ∧ (c8FourActionBounded c8FourRecordData299)
    ∧ (c8FourActionCovered c8FourRecordData300)
    ∧ (c8FourActionBounded c8FourRecordData300)
    ∧ (c8FourActionCovered c8FourRecordData301)
    ∧ (c8FourActionBounded c8FourRecordData301)
    ∧ (c8FourActionCovered c8FourRecordData302)
    ∧ (c8FourActionBounded c8FourRecordData302)
    ∧ (c8FourActionCovered c8FourRecordData303)
    ∧ (c8FourActionBounded c8FourRecordData303)
    ∧ (c8FourActionCovered c8FourRecordData304)
    ∧ (c8FourActionBounded c8FourRecordData304)
    ∧ (c8FourActionCovered c8FourRecordData305)
    ∧ (c8FourActionBounded c8FourRecordData305)
    ∧ (c8FourActionCovered c8FourRecordData306)
    ∧ (c8FourActionBounded c8FourRecordData306)
    ∧ (c8FourActionCovered c8FourRecordData307)
    ∧ (c8FourActionBounded c8FourRecordData307)
    ∧ (c8FourActionCovered c8FourRecordData308)
    ∧ (c8FourActionBounded c8FourRecordData308)
    ∧ (c8FourActionCovered c8FourRecordData309)
    ∧ (c8FourActionBounded c8FourRecordData309)
    ∧ (c8FourActionCovered c8FourRecordData310)
    ∧ (c8FourActionBounded c8FourRecordData310)
    ∧ (c8FourActionCovered c8FourRecordData311)
    ∧ (c8FourActionBounded c8FourRecordData311)
    ∧ (c8FourActionCovered c8FourRecordData312)
    ∧ (c8FourActionBounded c8FourRecordData312)
    ∧ (c8FourActionCovered c8FourRecordData313)
    ∧ (c8FourActionBounded c8FourRecordData313)
    ∧ (c8FourActionCovered c8FourRecordData314)
    ∧ (c8FourActionBounded c8FourRecordData314)
    ∧ (c8FourActionCovered c8FourRecordData315)
    ∧ (c8FourActionBounded c8FourRecordData315)
    ∧ (c8FourActionCovered c8FourRecordData316)
    ∧ (c8FourActionBounded c8FourRecordData316)
    ∧ (c8FourActionCovered c8FourRecordData317)
    ∧ (c8FourActionBounded c8FourRecordData317)
    ∧ (c8FourActionCovered c8FourRecordData318)
    ∧ (c8FourActionBounded c8FourRecordData318)
    ∧ (c8FourActionCovered c8FourRecordData319)
    ∧ (c8FourActionBounded c8FourRecordData319) := by
  exact ⟨CertificateChecks.Batch104.c8FourActionRecord256_covered, CertificateChecks.Batch104.c8FourActionRecord256_bounded, CertificateChecks.Batch104.c8FourActionRecord257_covered, CertificateChecks.Batch104.c8FourActionRecord257_bounded, CertificateChecks.Batch104.c8FourActionRecord258_covered, CertificateChecks.Batch104.c8FourActionRecord258_bounded, CertificateChecks.Batch104.c8FourActionRecord259_covered, CertificateChecks.Batch104.c8FourActionRecord259_bounded, CertificateChecks.Batch104.c8FourActionRecord260_covered, CertificateChecks.Batch104.c8FourActionRecord260_bounded, CertificateChecks.Batch104.c8FourActionRecord261_covered, CertificateChecks.Batch104.c8FourActionRecord261_bounded, CertificateChecks.Batch104.c8FourActionRecord262_covered, CertificateChecks.Batch104.c8FourActionRecord262_bounded, CertificateChecks.Batch104.c8FourActionRecord263_covered, CertificateChecks.Batch104.c8FourActionRecord263_bounded, CertificateChecks.Batch104.c8FourActionRecord264_covered, CertificateChecks.Batch104.c8FourActionRecord264_bounded, CertificateChecks.Batch104.c8FourActionRecord265_covered, CertificateChecks.Batch104.c8FourActionRecord265_bounded, CertificateChecks.Batch104.c8FourActionRecord266_covered, CertificateChecks.Batch104.c8FourActionRecord266_bounded, CertificateChecks.Batch104.c8FourActionRecord267_covered, CertificateChecks.Batch104.c8FourActionRecord267_bounded, CertificateChecks.Batch104.c8FourActionRecord268_covered, CertificateChecks.Batch104.c8FourActionRecord268_bounded, CertificateChecks.Batch104.c8FourActionRecord269_covered, CertificateChecks.Batch104.c8FourActionRecord269_bounded, CertificateChecks.Batch104.c8FourActionRecord270_covered, CertificateChecks.Batch104.c8FourActionRecord270_bounded, CertificateChecks.Batch104.c8FourActionRecord271_covered, CertificateChecks.Batch104.c8FourActionRecord271_bounded, CertificateChecks.Batch104.c8FourActionRecord272_covered, CertificateChecks.Batch104.c8FourActionRecord272_bounded, CertificateChecks.Batch104.c8FourActionRecord273_covered, CertificateChecks.Batch104.c8FourActionRecord273_bounded, CertificateChecks.Batch104.c8FourActionRecord274_covered, CertificateChecks.Batch104.c8FourActionRecord274_bounded, CertificateChecks.Batch104.c8FourActionRecord275_covered, CertificateChecks.Batch104.c8FourActionRecord275_bounded, CertificateChecks.Batch104.c8FourActionRecord276_covered, CertificateChecks.Batch104.c8FourActionRecord276_bounded, CertificateChecks.Batch104.c8FourActionRecord277_covered, CertificateChecks.Batch104.c8FourActionRecord277_bounded, CertificateChecks.Batch104.c8FourActionRecord278_covered, CertificateChecks.Batch104.c8FourActionRecord278_bounded, CertificateChecks.Batch104.c8FourActionRecord279_covered, CertificateChecks.Batch104.c8FourActionRecord279_bounded, CertificateChecks.Batch104.c8FourActionRecord280_covered, CertificateChecks.Batch104.c8FourActionRecord280_bounded, CertificateChecks.Batch104.c8FourActionRecord281_covered, CertificateChecks.Batch104.c8FourActionRecord281_bounded, CertificateChecks.Batch104.c8FourActionRecord282_covered, CertificateChecks.Batch104.c8FourActionRecord282_bounded, CertificateChecks.Batch104.c8FourActionRecord283_covered, CertificateChecks.Batch104.c8FourActionRecord283_bounded, CertificateChecks.Batch104.c8FourActionRecord284_covered, CertificateChecks.Batch104.c8FourActionRecord284_bounded, CertificateChecks.Batch104.c8FourActionRecord285_covered, CertificateChecks.Batch104.c8FourActionRecord285_bounded, CertificateChecks.Batch104.c8FourActionRecord286_covered, CertificateChecks.Batch104.c8FourActionRecord286_bounded, CertificateChecks.Batch104.c8FourActionRecord287_covered, CertificateChecks.Batch104.c8FourActionRecord287_bounded, CertificateChecks.Batch104.c8FourActionRecord288_covered, CertificateChecks.Batch104.c8FourActionRecord288_bounded, CertificateChecks.Batch104.c8FourActionRecord289_covered, CertificateChecks.Batch104.c8FourActionRecord289_bounded, CertificateChecks.Batch104.c8FourActionRecord290_covered, CertificateChecks.Batch104.c8FourActionRecord290_bounded, CertificateChecks.Batch104.c8FourActionRecord291_covered, CertificateChecks.Batch104.c8FourActionRecord291_bounded, CertificateChecks.Batch104.c8FourActionRecord292_covered, CertificateChecks.Batch104.c8FourActionRecord292_bounded, CertificateChecks.Batch104.c8FourActionRecord293_covered, CertificateChecks.Batch104.c8FourActionRecord293_bounded, CertificateChecks.Batch104.c8FourActionRecord294_covered, CertificateChecks.Batch104.c8FourActionRecord294_bounded, CertificateChecks.Batch104.c8FourActionRecord295_covered, CertificateChecks.Batch104.c8FourActionRecord295_bounded, CertificateChecks.Batch104.c8FourActionRecord296_covered, CertificateChecks.Batch104.c8FourActionRecord296_bounded, CertificateChecks.Batch104.c8FourActionRecord297_covered, CertificateChecks.Batch104.c8FourActionRecord297_bounded, CertificateChecks.Batch104.c8FourActionRecord298_covered, CertificateChecks.Batch104.c8FourActionRecord298_bounded, CertificateChecks.Batch104.c8FourActionRecord299_covered, CertificateChecks.Batch104.c8FourActionRecord299_bounded, CertificateChecks.Batch104.c8FourActionRecord300_covered, CertificateChecks.Batch104.c8FourActionRecord300_bounded, CertificateChecks.Batch104.c8FourActionRecord301_covered, CertificateChecks.Batch104.c8FourActionRecord301_bounded, CertificateChecks.Batch104.c8FourActionRecord302_covered, CertificateChecks.Batch104.c8FourActionRecord302_bounded, CertificateChecks.Batch104.c8FourActionRecord303_covered, CertificateChecks.Batch104.c8FourActionRecord303_bounded, CertificateChecks.Batch104.c8FourActionRecord304_covered, CertificateChecks.Batch104.c8FourActionRecord304_bounded, CertificateChecks.Batch104.c8FourActionRecord305_covered, CertificateChecks.Batch104.c8FourActionRecord305_bounded, CertificateChecks.Batch104.c8FourActionRecord306_covered, CertificateChecks.Batch104.c8FourActionRecord306_bounded, CertificateChecks.Batch104.c8FourActionRecord307_covered, CertificateChecks.Batch104.c8FourActionRecord307_bounded, CertificateChecks.Batch104.c8FourActionRecord308_covered, CertificateChecks.Batch104.c8FourActionRecord308_bounded, CertificateChecks.Batch104.c8FourActionRecord309_covered, CertificateChecks.Batch104.c8FourActionRecord309_bounded, CertificateChecks.Batch104.c8FourActionRecord310_covered, CertificateChecks.Batch104.c8FourActionRecord310_bounded, CertificateChecks.Batch104.c8FourActionRecord311_covered, CertificateChecks.Batch104.c8FourActionRecord311_bounded, CertificateChecks.Batch104.c8FourActionRecord312_covered, CertificateChecks.Batch104.c8FourActionRecord312_bounded, CertificateChecks.Batch104.c8FourActionRecord313_covered, CertificateChecks.Batch104.c8FourActionRecord313_bounded, CertificateChecks.Batch104.c8FourActionRecord314_covered, CertificateChecks.Batch104.c8FourActionRecord314_bounded, CertificateChecks.Batch104.c8FourActionRecord315_covered, CertificateChecks.Batch104.c8FourActionRecord315_bounded, CertificateChecks.Batch104.c8FourActionRecord316_covered, CertificateChecks.Batch104.c8FourActionRecord316_bounded, CertificateChecks.Batch104.c8FourActionRecord317_covered, CertificateChecks.Batch104.c8FourActionRecord317_bounded, CertificateChecks.Batch104.c8FourActionRecord318_covered, CertificateChecks.Batch104.c8FourActionRecord318_bounded, CertificateChecks.Batch104.c8FourActionRecord319_covered, CertificateChecks.Batch104.c8FourActionRecord319_bounded⟩

end Certificates
