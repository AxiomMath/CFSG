module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnessesCore

public section

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

namespace CertificateChecks.Batch106

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem c8FourActionRecord384_covered : c8FourActionCovered c8FourRecordData384 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨34, ?_⟩
  decide +kernel

private theorem c8FourActionRecord384_bounded : c8FourActionBounded c8FourRecordData384 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord385_covered : c8FourActionCovered c8FourRecordData385 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord385_bounded : c8FourActionBounded c8FourRecordData385 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord386_covered : c8FourActionCovered c8FourRecordData386 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord386_bounded : c8FourActionBounded c8FourRecordData386 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord387_covered : c8FourActionCovered c8FourRecordData387 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord387_bounded : c8FourActionBounded c8FourRecordData387 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord388_covered : c8FourActionCovered c8FourRecordData388 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord388_bounded : c8FourActionBounded c8FourRecordData388 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord389_covered : c8FourActionCovered c8FourRecordData389 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord389_bounded : c8FourActionBounded c8FourRecordData389 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord390_covered : c8FourActionCovered c8FourRecordData390 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord390_bounded : c8FourActionBounded c8FourRecordData390 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord391_covered : c8FourActionCovered c8FourRecordData391 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord391_bounded : c8FourActionBounded c8FourRecordData391 := by
  decide +kernel

private theorem c8FourActionRecord392_covered : c8FourActionCovered c8FourRecordData392 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord392_bounded : c8FourActionBounded c8FourRecordData392 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord393_covered : c8FourActionCovered c8FourRecordData393 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord393_bounded : c8FourActionBounded c8FourRecordData393 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord394_covered : c8FourActionCovered c8FourRecordData394 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord394_bounded : c8FourActionBounded c8FourRecordData394 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord395_covered : c8FourActionCovered c8FourRecordData395 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord395_bounded : c8FourActionBounded c8FourRecordData395 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord396_covered : c8FourActionCovered c8FourRecordData396 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord396_bounded : c8FourActionBounded c8FourRecordData396 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord397_covered : c8FourActionCovered c8FourRecordData397 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord397_bounded : c8FourActionBounded c8FourRecordData397 := by
  decide +kernel

private theorem c8FourActionRecord398_covered : c8FourActionCovered c8FourRecordData398 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨20, ?_⟩
  decide +kernel

private theorem c8FourActionRecord398_bounded : c8FourActionBounded c8FourRecordData398 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord399_covered : c8FourActionCovered c8FourRecordData399 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨20, ?_⟩
  decide +kernel

private theorem c8FourActionRecord399_bounded : c8FourActionBounded c8FourRecordData399 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord400_covered : c8FourActionCovered c8FourRecordData400 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨20, ?_⟩
  decide +kernel

private theorem c8FourActionRecord400_bounded : c8FourActionBounded c8FourRecordData400 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord401_covered : c8FourActionCovered c8FourRecordData401 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨20, ?_⟩
  decide +kernel

private theorem c8FourActionRecord401_bounded : c8FourActionBounded c8FourRecordData401 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord402_covered : c8FourActionCovered c8FourRecordData402 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨20, ?_⟩
  decide +kernel

private theorem c8FourActionRecord402_bounded : c8FourActionBounded c8FourRecordData402 := by
  decide +kernel

private theorem c8FourActionRecord403_covered : c8FourActionCovered c8FourRecordData403 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨6, ?_⟩
  decide +kernel

private theorem c8FourActionRecord403_bounded : c8FourActionBounded c8FourRecordData403 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord404_covered : c8FourActionCovered c8FourRecordData404 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord404_bounded : c8FourActionBounded c8FourRecordData404 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord405_covered : c8FourActionCovered c8FourRecordData405 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord405_bounded : c8FourActionBounded c8FourRecordData405 := by
  decide +kernel

private theorem c8FourActionRecord406_covered : c8FourActionCovered c8FourRecordData406 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨23, ?_⟩
  decide +kernel

private theorem c8FourActionRecord406_bounded : c8FourActionBounded c8FourRecordData406 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord407_covered : c8FourActionCovered c8FourRecordData407 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord407_bounded : c8FourActionBounded c8FourRecordData407 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord408_covered : c8FourActionCovered c8FourRecordData408 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨26, ?_⟩
  decide +kernel

private theorem c8FourActionRecord408_bounded : c8FourActionBounded c8FourRecordData408 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord409_covered : c8FourActionCovered c8FourRecordData409 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨23, ?_⟩
  decide +kernel

private theorem c8FourActionRecord409_bounded : c8FourActionBounded c8FourRecordData409 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord410_covered : c8FourActionCovered c8FourRecordData410 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨23, ?_⟩
  decide +kernel

private theorem c8FourActionRecord410_bounded : c8FourActionBounded c8FourRecordData410 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord411_covered : c8FourActionCovered c8FourRecordData411 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord411_bounded : c8FourActionBounded c8FourRecordData411 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord412_covered : c8FourActionCovered c8FourRecordData412 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨25, ?_⟩
  decide +kernel

private theorem c8FourActionRecord412_bounded : c8FourActionBounded c8FourRecordData412 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord413_covered : c8FourActionCovered c8FourRecordData413 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord413_bounded : c8FourActionBounded c8FourRecordData413 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord414_covered : c8FourActionCovered c8FourRecordData414 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨24, ?_⟩
  decide +kernel

private theorem c8FourActionRecord414_bounded : c8FourActionBounded c8FourRecordData414 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord415_covered : c8FourActionCovered c8FourRecordData415 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord415_bounded : c8FourActionBounded c8FourRecordData415 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord416_covered : c8FourActionCovered c8FourRecordData416 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord416_bounded : c8FourActionBounded c8FourRecordData416 := by
  decide +kernel

private theorem c8FourActionRecord417_covered : c8FourActionCovered c8FourRecordData417 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord417_bounded : c8FourActionBounded c8FourRecordData417 := by
  decide +kernel

private theorem c8FourActionRecord418_covered : c8FourActionCovered c8FourRecordData418 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord418_bounded : c8FourActionBounded c8FourRecordData418 := by
  decide +kernel

private theorem c8FourActionRecord419_covered : c8FourActionCovered c8FourRecordData419 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord419_bounded : c8FourActionBounded c8FourRecordData419 := by
  decide +kernel

private theorem c8FourActionRecord420_covered : c8FourActionCovered c8FourRecordData420 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord420_bounded : c8FourActionBounded c8FourRecordData420 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord421_covered : c8FourActionCovered c8FourRecordData421 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord421_bounded : c8FourActionBounded c8FourRecordData421 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord422_covered : c8FourActionCovered c8FourRecordData422 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨24, ?_⟩
  decide +kernel

private theorem c8FourActionRecord422_bounded : c8FourActionBounded c8FourRecordData422 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord423_covered : c8FourActionCovered c8FourRecordData423 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord423_bounded : c8FourActionBounded c8FourRecordData423 := by
  decide +kernel

private theorem c8FourActionRecord424_covered : c8FourActionCovered c8FourRecordData424 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord424_bounded : c8FourActionBounded c8FourRecordData424 := by
  decide +kernel

private theorem c8FourActionRecord425_covered : c8FourActionCovered c8FourRecordData425 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord425_bounded : c8FourActionBounded c8FourRecordData425 := by
  decide +kernel

private theorem c8FourActionRecord426_covered : c8FourActionCovered c8FourRecordData426 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨24, ?_⟩
  decide +kernel

private theorem c8FourActionRecord426_bounded : c8FourActionBounded c8FourRecordData426 := by
  decide +kernel

private theorem c8FourActionRecord427_covered : c8FourActionCovered c8FourRecordData427 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨24, ?_⟩
  decide +kernel

private theorem c8FourActionRecord427_bounded : c8FourActionBounded c8FourRecordData427 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord428_covered : c8FourActionCovered c8FourRecordData428 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord428_bounded : c8FourActionBounded c8FourRecordData428 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord429_covered : c8FourActionCovered c8FourRecordData429 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord429_bounded : c8FourActionBounded c8FourRecordData429 := by
  decide +kernel

private theorem c8FourActionRecord430_covered : c8FourActionCovered c8FourRecordData430 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord430_bounded : c8FourActionBounded c8FourRecordData430 := by
  decide +kernel

private theorem c8FourActionRecord431_covered : c8FourActionCovered c8FourRecordData431 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord431_bounded : c8FourActionBounded c8FourRecordData431 := by
  decide +kernel

private theorem c8FourActionRecord432_covered : c8FourActionCovered c8FourRecordData432 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord432_bounded : c8FourActionBounded c8FourRecordData432 := by
  decide +kernel

private theorem c8FourActionRecord433_covered : c8FourActionCovered c8FourRecordData433 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨25, ?_⟩
  decide +kernel

private theorem c8FourActionRecord433_bounded : c8FourActionBounded c8FourRecordData433 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord434_covered : c8FourActionCovered c8FourRecordData434 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord434_bounded : c8FourActionBounded c8FourRecordData434 := by
  decide +kernel

private theorem c8FourActionRecord435_covered : c8FourActionCovered c8FourRecordData435 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨25, ?_⟩
  decide +kernel

private theorem c8FourActionRecord435_bounded : c8FourActionBounded c8FourRecordData435 := by
  decide +kernel

private theorem c8FourActionRecord436_covered : c8FourActionCovered c8FourRecordData436 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord436_bounded : c8FourActionBounded c8FourRecordData436 := by
  decide +kernel

private theorem c8FourActionRecord437_covered : c8FourActionCovered c8FourRecordData437 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord437_bounded : c8FourActionBounded c8FourRecordData437 := by
  decide +kernel

private theorem c8FourActionRecord438_covered : c8FourActionCovered c8FourRecordData438 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨25, ?_⟩
  decide +kernel

private theorem c8FourActionRecord438_bounded : c8FourActionBounded c8FourRecordData438 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord439_covered : c8FourActionCovered c8FourRecordData439 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨21, ?_⟩
  decide +kernel

private theorem c8FourActionRecord439_bounded : c8FourActionBounded c8FourRecordData439 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord440_covered : c8FourActionCovered c8FourRecordData440 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord440_bounded : c8FourActionBounded c8FourRecordData440 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord441_covered : c8FourActionCovered c8FourRecordData441 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨29, ?_⟩
  decide +kernel

private theorem c8FourActionRecord441_bounded : c8FourActionBounded c8FourRecordData441 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord442_covered : c8FourActionCovered c8FourRecordData442 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨21, ?_⟩
  decide +kernel

private theorem c8FourActionRecord442_bounded : c8FourActionBounded c8FourRecordData442 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord443_covered : c8FourActionCovered c8FourRecordData443 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨23, ?_⟩
  decide +kernel

private theorem c8FourActionRecord443_bounded : c8FourActionBounded c8FourRecordData443 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord444_covered : c8FourActionCovered c8FourRecordData444 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord444_bounded : c8FourActionBounded c8FourRecordData444 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord445_covered : c8FourActionCovered c8FourRecordData445 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord445_bounded : c8FourActionBounded c8FourRecordData445 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord446_covered : c8FourActionCovered c8FourRecordData446 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨22, ?_⟩
  decide +kernel

private theorem c8FourActionRecord446_bounded : c8FourActionBounded c8FourRecordData446 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord447_covered : c8FourActionCovered c8FourRecordData447 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord447_bounded : c8FourActionBounded c8FourRecordData447 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionChunk6_covered (j : Fin 64) :
    c8FourActionCovered (c8FourRecordChunk6[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord384_covered
  · exact c8FourActionRecord385_covered
  · exact c8FourActionRecord386_covered
  · exact c8FourActionRecord387_covered
  · exact c8FourActionRecord388_covered
  · exact c8FourActionRecord389_covered
  · exact c8FourActionRecord390_covered
  · exact c8FourActionRecord391_covered
  · exact c8FourActionRecord392_covered
  · exact c8FourActionRecord393_covered
  · exact c8FourActionRecord394_covered
  · exact c8FourActionRecord395_covered
  · exact c8FourActionRecord396_covered
  · exact c8FourActionRecord397_covered
  · exact c8FourActionRecord398_covered
  · exact c8FourActionRecord399_covered
  · exact c8FourActionRecord400_covered
  · exact c8FourActionRecord401_covered
  · exact c8FourActionRecord402_covered
  · exact c8FourActionRecord403_covered
  · exact c8FourActionRecord404_covered
  · exact c8FourActionRecord405_covered
  · exact c8FourActionRecord406_covered
  · exact c8FourActionRecord407_covered
  · exact c8FourActionRecord408_covered
  · exact c8FourActionRecord409_covered
  · exact c8FourActionRecord410_covered
  · exact c8FourActionRecord411_covered
  · exact c8FourActionRecord412_covered
  · exact c8FourActionRecord413_covered
  · exact c8FourActionRecord414_covered
  · exact c8FourActionRecord415_covered
  · exact c8FourActionRecord416_covered
  · exact c8FourActionRecord417_covered
  · exact c8FourActionRecord418_covered
  · exact c8FourActionRecord419_covered
  · exact c8FourActionRecord420_covered
  · exact c8FourActionRecord421_covered
  · exact c8FourActionRecord422_covered
  · exact c8FourActionRecord423_covered
  · exact c8FourActionRecord424_covered
  · exact c8FourActionRecord425_covered
  · exact c8FourActionRecord426_covered
  · exact c8FourActionRecord427_covered
  · exact c8FourActionRecord428_covered
  · exact c8FourActionRecord429_covered
  · exact c8FourActionRecord430_covered
  · exact c8FourActionRecord431_covered
  · exact c8FourActionRecord432_covered
  · exact c8FourActionRecord433_covered
  · exact c8FourActionRecord434_covered
  · exact c8FourActionRecord435_covered
  · exact c8FourActionRecord436_covered
  · exact c8FourActionRecord437_covered
  · exact c8FourActionRecord438_covered
  · exact c8FourActionRecord439_covered
  · exact c8FourActionRecord440_covered
  · exact c8FourActionRecord441_covered
  · exact c8FourActionRecord442_covered
  · exact c8FourActionRecord443_covered
  · exact c8FourActionRecord444_covered
  · exact c8FourActionRecord445_covered
  · exact c8FourActionRecord446_covered
  · exact c8FourActionRecord447_covered

private theorem c8FourActionChunk6_bounded (j : Fin 64) :
    c8FourActionBounded (c8FourRecordChunk6[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord384_bounded
  · exact c8FourActionRecord385_bounded
  · exact c8FourActionRecord386_bounded
  · exact c8FourActionRecord387_bounded
  · exact c8FourActionRecord388_bounded
  · exact c8FourActionRecord389_bounded
  · exact c8FourActionRecord390_bounded
  · exact c8FourActionRecord391_bounded
  · exact c8FourActionRecord392_bounded
  · exact c8FourActionRecord393_bounded
  · exact c8FourActionRecord394_bounded
  · exact c8FourActionRecord395_bounded
  · exact c8FourActionRecord396_bounded
  · exact c8FourActionRecord397_bounded
  · exact c8FourActionRecord398_bounded
  · exact c8FourActionRecord399_bounded
  · exact c8FourActionRecord400_bounded
  · exact c8FourActionRecord401_bounded
  · exact c8FourActionRecord402_bounded
  · exact c8FourActionRecord403_bounded
  · exact c8FourActionRecord404_bounded
  · exact c8FourActionRecord405_bounded
  · exact c8FourActionRecord406_bounded
  · exact c8FourActionRecord407_bounded
  · exact c8FourActionRecord408_bounded
  · exact c8FourActionRecord409_bounded
  · exact c8FourActionRecord410_bounded
  · exact c8FourActionRecord411_bounded
  · exact c8FourActionRecord412_bounded
  · exact c8FourActionRecord413_bounded
  · exact c8FourActionRecord414_bounded
  · exact c8FourActionRecord415_bounded
  · exact c8FourActionRecord416_bounded
  · exact c8FourActionRecord417_bounded
  · exact c8FourActionRecord418_bounded
  · exact c8FourActionRecord419_bounded
  · exact c8FourActionRecord420_bounded
  · exact c8FourActionRecord421_bounded
  · exact c8FourActionRecord422_bounded
  · exact c8FourActionRecord423_bounded
  · exact c8FourActionRecord424_bounded
  · exact c8FourActionRecord425_bounded
  · exact c8FourActionRecord426_bounded
  · exact c8FourActionRecord427_bounded
  · exact c8FourActionRecord428_bounded
  · exact c8FourActionRecord429_bounded
  · exact c8FourActionRecord430_bounded
  · exact c8FourActionRecord431_bounded
  · exact c8FourActionRecord432_bounded
  · exact c8FourActionRecord433_bounded
  · exact c8FourActionRecord434_bounded
  · exact c8FourActionRecord435_bounded
  · exact c8FourActionRecord436_bounded
  · exact c8FourActionRecord437_bounded
  · exact c8FourActionRecord438_bounded
  · exact c8FourActionRecord439_bounded
  · exact c8FourActionRecord440_bounded
  · exact c8FourActionRecord441_bounded
  · exact c8FourActionRecord442_bounded
  · exact c8FourActionRecord443_bounded
  · exact c8FourActionRecord444_bounded
  · exact c8FourActionRecord445_bounded
  · exact c8FourActionRecord446_bounded
  · exact c8FourActionRecord447_bounded

end CertificateChecks.Batch106

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers in
theorem certificate106 : (c8FourActionCovered c8FourRecordData384)
    ∧ (c8FourActionBounded c8FourRecordData384)
    ∧ (c8FourActionCovered c8FourRecordData385)
    ∧ (c8FourActionBounded c8FourRecordData385)
    ∧ (c8FourActionCovered c8FourRecordData386)
    ∧ (c8FourActionBounded c8FourRecordData386)
    ∧ (c8FourActionCovered c8FourRecordData387)
    ∧ (c8FourActionBounded c8FourRecordData387)
    ∧ (c8FourActionCovered c8FourRecordData388)
    ∧ (c8FourActionBounded c8FourRecordData388)
    ∧ (c8FourActionCovered c8FourRecordData389)
    ∧ (c8FourActionBounded c8FourRecordData389)
    ∧ (c8FourActionCovered c8FourRecordData390)
    ∧ (c8FourActionBounded c8FourRecordData390)
    ∧ (c8FourActionCovered c8FourRecordData391)
    ∧ (c8FourActionBounded c8FourRecordData391)
    ∧ (c8FourActionCovered c8FourRecordData392)
    ∧ (c8FourActionBounded c8FourRecordData392)
    ∧ (c8FourActionCovered c8FourRecordData393)
    ∧ (c8FourActionBounded c8FourRecordData393)
    ∧ (c8FourActionCovered c8FourRecordData394)
    ∧ (c8FourActionBounded c8FourRecordData394)
    ∧ (c8FourActionCovered c8FourRecordData395)
    ∧ (c8FourActionBounded c8FourRecordData395)
    ∧ (c8FourActionCovered c8FourRecordData396)
    ∧ (c8FourActionBounded c8FourRecordData396)
    ∧ (c8FourActionCovered c8FourRecordData397)
    ∧ (c8FourActionBounded c8FourRecordData397)
    ∧ (c8FourActionCovered c8FourRecordData398)
    ∧ (c8FourActionBounded c8FourRecordData398)
    ∧ (c8FourActionCovered c8FourRecordData399)
    ∧ (c8FourActionBounded c8FourRecordData399)
    ∧ (c8FourActionCovered c8FourRecordData400)
    ∧ (c8FourActionBounded c8FourRecordData400)
    ∧ (c8FourActionCovered c8FourRecordData401)
    ∧ (c8FourActionBounded c8FourRecordData401)
    ∧ (c8FourActionCovered c8FourRecordData402)
    ∧ (c8FourActionBounded c8FourRecordData402)
    ∧ (c8FourActionCovered c8FourRecordData403)
    ∧ (c8FourActionBounded c8FourRecordData403)
    ∧ (c8FourActionCovered c8FourRecordData404)
    ∧ (c8FourActionBounded c8FourRecordData404)
    ∧ (c8FourActionCovered c8FourRecordData405)
    ∧ (c8FourActionBounded c8FourRecordData405)
    ∧ (c8FourActionCovered c8FourRecordData406)
    ∧ (c8FourActionBounded c8FourRecordData406)
    ∧ (c8FourActionCovered c8FourRecordData407)
    ∧ (c8FourActionBounded c8FourRecordData407)
    ∧ (c8FourActionCovered c8FourRecordData408)
    ∧ (c8FourActionBounded c8FourRecordData408)
    ∧ (c8FourActionCovered c8FourRecordData409)
    ∧ (c8FourActionBounded c8FourRecordData409)
    ∧ (c8FourActionCovered c8FourRecordData410)
    ∧ (c8FourActionBounded c8FourRecordData410)
    ∧ (c8FourActionCovered c8FourRecordData411)
    ∧ (c8FourActionBounded c8FourRecordData411)
    ∧ (c8FourActionCovered c8FourRecordData412)
    ∧ (c8FourActionBounded c8FourRecordData412)
    ∧ (c8FourActionCovered c8FourRecordData413)
    ∧ (c8FourActionBounded c8FourRecordData413)
    ∧ (c8FourActionCovered c8FourRecordData414)
    ∧ (c8FourActionBounded c8FourRecordData414)
    ∧ (c8FourActionCovered c8FourRecordData415)
    ∧ (c8FourActionBounded c8FourRecordData415)
    ∧ (c8FourActionCovered c8FourRecordData416)
    ∧ (c8FourActionBounded c8FourRecordData416)
    ∧ (c8FourActionCovered c8FourRecordData417)
    ∧ (c8FourActionBounded c8FourRecordData417)
    ∧ (c8FourActionCovered c8FourRecordData418)
    ∧ (c8FourActionBounded c8FourRecordData418)
    ∧ (c8FourActionCovered c8FourRecordData419)
    ∧ (c8FourActionBounded c8FourRecordData419)
    ∧ (c8FourActionCovered c8FourRecordData420)
    ∧ (c8FourActionBounded c8FourRecordData420)
    ∧ (c8FourActionCovered c8FourRecordData421)
    ∧ (c8FourActionBounded c8FourRecordData421)
    ∧ (c8FourActionCovered c8FourRecordData422)
    ∧ (c8FourActionBounded c8FourRecordData422)
    ∧ (c8FourActionCovered c8FourRecordData423)
    ∧ (c8FourActionBounded c8FourRecordData423)
    ∧ (c8FourActionCovered c8FourRecordData424)
    ∧ (c8FourActionBounded c8FourRecordData424)
    ∧ (c8FourActionCovered c8FourRecordData425)
    ∧ (c8FourActionBounded c8FourRecordData425)
    ∧ (c8FourActionCovered c8FourRecordData426)
    ∧ (c8FourActionBounded c8FourRecordData426)
    ∧ (c8FourActionCovered c8FourRecordData427)
    ∧ (c8FourActionBounded c8FourRecordData427)
    ∧ (c8FourActionCovered c8FourRecordData428)
    ∧ (c8FourActionBounded c8FourRecordData428)
    ∧ (c8FourActionCovered c8FourRecordData429)
    ∧ (c8FourActionBounded c8FourRecordData429)
    ∧ (c8FourActionCovered c8FourRecordData430)
    ∧ (c8FourActionBounded c8FourRecordData430)
    ∧ (c8FourActionCovered c8FourRecordData431)
    ∧ (c8FourActionBounded c8FourRecordData431)
    ∧ (c8FourActionCovered c8FourRecordData432)
    ∧ (c8FourActionBounded c8FourRecordData432)
    ∧ (c8FourActionCovered c8FourRecordData433)
    ∧ (c8FourActionBounded c8FourRecordData433)
    ∧ (c8FourActionCovered c8FourRecordData434)
    ∧ (c8FourActionBounded c8FourRecordData434)
    ∧ (c8FourActionCovered c8FourRecordData435)
    ∧ (c8FourActionBounded c8FourRecordData435)
    ∧ (c8FourActionCovered c8FourRecordData436)
    ∧ (c8FourActionBounded c8FourRecordData436)
    ∧ (c8FourActionCovered c8FourRecordData437)
    ∧ (c8FourActionBounded c8FourRecordData437)
    ∧ (c8FourActionCovered c8FourRecordData438)
    ∧ (c8FourActionBounded c8FourRecordData438)
    ∧ (c8FourActionCovered c8FourRecordData439)
    ∧ (c8FourActionBounded c8FourRecordData439)
    ∧ (c8FourActionCovered c8FourRecordData440)
    ∧ (c8FourActionBounded c8FourRecordData440)
    ∧ (c8FourActionCovered c8FourRecordData441)
    ∧ (c8FourActionBounded c8FourRecordData441)
    ∧ (c8FourActionCovered c8FourRecordData442)
    ∧ (c8FourActionBounded c8FourRecordData442)
    ∧ (c8FourActionCovered c8FourRecordData443)
    ∧ (c8FourActionBounded c8FourRecordData443)
    ∧ (c8FourActionCovered c8FourRecordData444)
    ∧ (c8FourActionBounded c8FourRecordData444)
    ∧ (c8FourActionCovered c8FourRecordData445)
    ∧ (c8FourActionBounded c8FourRecordData445)
    ∧ (c8FourActionCovered c8FourRecordData446)
    ∧ (c8FourActionBounded c8FourRecordData446)
    ∧ (c8FourActionCovered c8FourRecordData447)
    ∧ (c8FourActionBounded c8FourRecordData447) := by
  exact ⟨CertificateChecks.Batch106.c8FourActionRecord384_covered, CertificateChecks.Batch106.c8FourActionRecord384_bounded, CertificateChecks.Batch106.c8FourActionRecord385_covered, CertificateChecks.Batch106.c8FourActionRecord385_bounded, CertificateChecks.Batch106.c8FourActionRecord386_covered, CertificateChecks.Batch106.c8FourActionRecord386_bounded, CertificateChecks.Batch106.c8FourActionRecord387_covered, CertificateChecks.Batch106.c8FourActionRecord387_bounded, CertificateChecks.Batch106.c8FourActionRecord388_covered, CertificateChecks.Batch106.c8FourActionRecord388_bounded, CertificateChecks.Batch106.c8FourActionRecord389_covered, CertificateChecks.Batch106.c8FourActionRecord389_bounded, CertificateChecks.Batch106.c8FourActionRecord390_covered, CertificateChecks.Batch106.c8FourActionRecord390_bounded, CertificateChecks.Batch106.c8FourActionRecord391_covered, CertificateChecks.Batch106.c8FourActionRecord391_bounded, CertificateChecks.Batch106.c8FourActionRecord392_covered, CertificateChecks.Batch106.c8FourActionRecord392_bounded, CertificateChecks.Batch106.c8FourActionRecord393_covered, CertificateChecks.Batch106.c8FourActionRecord393_bounded, CertificateChecks.Batch106.c8FourActionRecord394_covered, CertificateChecks.Batch106.c8FourActionRecord394_bounded, CertificateChecks.Batch106.c8FourActionRecord395_covered, CertificateChecks.Batch106.c8FourActionRecord395_bounded, CertificateChecks.Batch106.c8FourActionRecord396_covered, CertificateChecks.Batch106.c8FourActionRecord396_bounded, CertificateChecks.Batch106.c8FourActionRecord397_covered, CertificateChecks.Batch106.c8FourActionRecord397_bounded, CertificateChecks.Batch106.c8FourActionRecord398_covered, CertificateChecks.Batch106.c8FourActionRecord398_bounded, CertificateChecks.Batch106.c8FourActionRecord399_covered, CertificateChecks.Batch106.c8FourActionRecord399_bounded, CertificateChecks.Batch106.c8FourActionRecord400_covered, CertificateChecks.Batch106.c8FourActionRecord400_bounded, CertificateChecks.Batch106.c8FourActionRecord401_covered, CertificateChecks.Batch106.c8FourActionRecord401_bounded, CertificateChecks.Batch106.c8FourActionRecord402_covered, CertificateChecks.Batch106.c8FourActionRecord402_bounded, CertificateChecks.Batch106.c8FourActionRecord403_covered, CertificateChecks.Batch106.c8FourActionRecord403_bounded, CertificateChecks.Batch106.c8FourActionRecord404_covered, CertificateChecks.Batch106.c8FourActionRecord404_bounded, CertificateChecks.Batch106.c8FourActionRecord405_covered, CertificateChecks.Batch106.c8FourActionRecord405_bounded, CertificateChecks.Batch106.c8FourActionRecord406_covered, CertificateChecks.Batch106.c8FourActionRecord406_bounded, CertificateChecks.Batch106.c8FourActionRecord407_covered, CertificateChecks.Batch106.c8FourActionRecord407_bounded, CertificateChecks.Batch106.c8FourActionRecord408_covered, CertificateChecks.Batch106.c8FourActionRecord408_bounded, CertificateChecks.Batch106.c8FourActionRecord409_covered, CertificateChecks.Batch106.c8FourActionRecord409_bounded, CertificateChecks.Batch106.c8FourActionRecord410_covered, CertificateChecks.Batch106.c8FourActionRecord410_bounded, CertificateChecks.Batch106.c8FourActionRecord411_covered, CertificateChecks.Batch106.c8FourActionRecord411_bounded, CertificateChecks.Batch106.c8FourActionRecord412_covered, CertificateChecks.Batch106.c8FourActionRecord412_bounded, CertificateChecks.Batch106.c8FourActionRecord413_covered, CertificateChecks.Batch106.c8FourActionRecord413_bounded, CertificateChecks.Batch106.c8FourActionRecord414_covered, CertificateChecks.Batch106.c8FourActionRecord414_bounded, CertificateChecks.Batch106.c8FourActionRecord415_covered, CertificateChecks.Batch106.c8FourActionRecord415_bounded, CertificateChecks.Batch106.c8FourActionRecord416_covered, CertificateChecks.Batch106.c8FourActionRecord416_bounded, CertificateChecks.Batch106.c8FourActionRecord417_covered, CertificateChecks.Batch106.c8FourActionRecord417_bounded, CertificateChecks.Batch106.c8FourActionRecord418_covered, CertificateChecks.Batch106.c8FourActionRecord418_bounded, CertificateChecks.Batch106.c8FourActionRecord419_covered, CertificateChecks.Batch106.c8FourActionRecord419_bounded, CertificateChecks.Batch106.c8FourActionRecord420_covered, CertificateChecks.Batch106.c8FourActionRecord420_bounded, CertificateChecks.Batch106.c8FourActionRecord421_covered, CertificateChecks.Batch106.c8FourActionRecord421_bounded, CertificateChecks.Batch106.c8FourActionRecord422_covered, CertificateChecks.Batch106.c8FourActionRecord422_bounded, CertificateChecks.Batch106.c8FourActionRecord423_covered, CertificateChecks.Batch106.c8FourActionRecord423_bounded, CertificateChecks.Batch106.c8FourActionRecord424_covered, CertificateChecks.Batch106.c8FourActionRecord424_bounded, CertificateChecks.Batch106.c8FourActionRecord425_covered, CertificateChecks.Batch106.c8FourActionRecord425_bounded, CertificateChecks.Batch106.c8FourActionRecord426_covered, CertificateChecks.Batch106.c8FourActionRecord426_bounded, CertificateChecks.Batch106.c8FourActionRecord427_covered, CertificateChecks.Batch106.c8FourActionRecord427_bounded, CertificateChecks.Batch106.c8FourActionRecord428_covered, CertificateChecks.Batch106.c8FourActionRecord428_bounded, CertificateChecks.Batch106.c8FourActionRecord429_covered, CertificateChecks.Batch106.c8FourActionRecord429_bounded, CertificateChecks.Batch106.c8FourActionRecord430_covered, CertificateChecks.Batch106.c8FourActionRecord430_bounded, CertificateChecks.Batch106.c8FourActionRecord431_covered, CertificateChecks.Batch106.c8FourActionRecord431_bounded, CertificateChecks.Batch106.c8FourActionRecord432_covered, CertificateChecks.Batch106.c8FourActionRecord432_bounded, CertificateChecks.Batch106.c8FourActionRecord433_covered, CertificateChecks.Batch106.c8FourActionRecord433_bounded, CertificateChecks.Batch106.c8FourActionRecord434_covered, CertificateChecks.Batch106.c8FourActionRecord434_bounded, CertificateChecks.Batch106.c8FourActionRecord435_covered, CertificateChecks.Batch106.c8FourActionRecord435_bounded, CertificateChecks.Batch106.c8FourActionRecord436_covered, CertificateChecks.Batch106.c8FourActionRecord436_bounded, CertificateChecks.Batch106.c8FourActionRecord437_covered, CertificateChecks.Batch106.c8FourActionRecord437_bounded, CertificateChecks.Batch106.c8FourActionRecord438_covered, CertificateChecks.Batch106.c8FourActionRecord438_bounded, CertificateChecks.Batch106.c8FourActionRecord439_covered, CertificateChecks.Batch106.c8FourActionRecord439_bounded, CertificateChecks.Batch106.c8FourActionRecord440_covered, CertificateChecks.Batch106.c8FourActionRecord440_bounded, CertificateChecks.Batch106.c8FourActionRecord441_covered, CertificateChecks.Batch106.c8FourActionRecord441_bounded, CertificateChecks.Batch106.c8FourActionRecord442_covered, CertificateChecks.Batch106.c8FourActionRecord442_bounded, CertificateChecks.Batch106.c8FourActionRecord443_covered, CertificateChecks.Batch106.c8FourActionRecord443_bounded, CertificateChecks.Batch106.c8FourActionRecord444_covered, CertificateChecks.Batch106.c8FourActionRecord444_bounded, CertificateChecks.Batch106.c8FourActionRecord445_covered, CertificateChecks.Batch106.c8FourActionRecord445_bounded, CertificateChecks.Batch106.c8FourActionRecord446_covered, CertificateChecks.Batch106.c8FourActionRecord446_bounded, CertificateChecks.Batch106.c8FourActionRecord447_covered, CertificateChecks.Batch106.c8FourActionRecord447_bounded⟩

end Certificates
