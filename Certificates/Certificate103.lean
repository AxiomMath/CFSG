module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnessesCore

public section

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

namespace CertificateChecks.Batch103

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem c8FourActionRecord192_covered : c8FourActionCovered c8FourRecordData192 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨30, ?_⟩
  decide +kernel

private theorem c8FourActionRecord192_bounded : c8FourActionBounded c8FourRecordData192 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord193_covered : c8FourActionCovered c8FourRecordData193 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord193_bounded : c8FourActionBounded c8FourRecordData193 := by
  decide +kernel

private theorem c8FourActionRecord194_covered : c8FourActionCovered c8FourRecordData194 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord194_bounded : c8FourActionBounded c8FourRecordData194 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord195_covered : c8FourActionCovered c8FourRecordData195 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord195_bounded : c8FourActionBounded c8FourRecordData195 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord196_covered : c8FourActionCovered c8FourRecordData196 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord196_bounded : c8FourActionBounded c8FourRecordData196 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord197_covered : c8FourActionCovered c8FourRecordData197 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord197_bounded : c8FourActionBounded c8FourRecordData197 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord198_covered : c8FourActionCovered c8FourRecordData198 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord198_bounded : c8FourActionBounded c8FourRecordData198 := by
  decide +kernel

private theorem c8FourActionRecord199_covered : c8FourActionCovered c8FourRecordData199 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord199_bounded : c8FourActionBounded c8FourRecordData199 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord200_covered : c8FourActionCovered c8FourRecordData200 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord200_bounded : c8FourActionBounded c8FourRecordData200 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord201_covered : c8FourActionCovered c8FourRecordData201 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord201_bounded : c8FourActionBounded c8FourRecordData201 := by
  decide +kernel

private theorem c8FourActionRecord202_covered : c8FourActionCovered c8FourRecordData202 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord202_bounded : c8FourActionBounded c8FourRecordData202 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord203_covered : c8FourActionCovered c8FourRecordData203 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord203_bounded : c8FourActionBounded c8FourRecordData203 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord204_covered : c8FourActionCovered c8FourRecordData204 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord204_bounded : c8FourActionBounded c8FourRecordData204 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord205_covered : c8FourActionCovered c8FourRecordData205 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord205_bounded : c8FourActionBounded c8FourRecordData205 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord206_covered : c8FourActionCovered c8FourRecordData206 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord206_bounded : c8FourActionBounded c8FourRecordData206 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord207_covered : c8FourActionCovered c8FourRecordData207 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord207_bounded : c8FourActionBounded c8FourRecordData207 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord208_covered : c8FourActionCovered c8FourRecordData208 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord208_bounded : c8FourActionBounded c8FourRecordData208 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord209_covered : c8FourActionCovered c8FourRecordData209 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord209_bounded : c8FourActionBounded c8FourRecordData209 := by
  decide +kernel

private theorem c8FourActionRecord210_covered : c8FourActionCovered c8FourRecordData210 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord210_bounded : c8FourActionBounded c8FourRecordData210 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord211_covered : c8FourActionCovered c8FourRecordData211 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord211_bounded : c8FourActionBounded c8FourRecordData211 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord212_covered : c8FourActionCovered c8FourRecordData212 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord212_bounded : c8FourActionBounded c8FourRecordData212 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord213_covered : c8FourActionCovered c8FourRecordData213 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord213_bounded : c8FourActionBounded c8FourRecordData213 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord214_covered : c8FourActionCovered c8FourRecordData214 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord214_bounded : c8FourActionBounded c8FourRecordData214 := by
  decide +kernel

private theorem c8FourActionRecord215_covered : c8FourActionCovered c8FourRecordData215 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord215_bounded : c8FourActionBounded c8FourRecordData215 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord216_covered : c8FourActionCovered c8FourRecordData216 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord216_bounded : c8FourActionBounded c8FourRecordData216 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord217_covered : c8FourActionCovered c8FourRecordData217 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord217_bounded : c8FourActionBounded c8FourRecordData217 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord218_covered : c8FourActionCovered c8FourRecordData218 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨3, ?_⟩
  decide +kernel

private theorem c8FourActionRecord218_bounded : c8FourActionBounded c8FourRecordData218 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord219_covered : c8FourActionCovered c8FourRecordData219 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord219_bounded : c8FourActionBounded c8FourRecordData219 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord220_covered : c8FourActionCovered c8FourRecordData220 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord220_bounded : c8FourActionBounded c8FourRecordData220 := by
  decide +kernel

private theorem c8FourActionRecord221_covered : c8FourActionCovered c8FourRecordData221 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord221_bounded : c8FourActionBounded c8FourRecordData221 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord222_covered : c8FourActionCovered c8FourRecordData222 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord222_bounded : c8FourActionBounded c8FourRecordData222 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord223_covered : c8FourActionCovered c8FourRecordData223 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord223_bounded : c8FourActionBounded c8FourRecordData223 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord224_covered : c8FourActionCovered c8FourRecordData224 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord224_bounded : c8FourActionBounded c8FourRecordData224 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord225_covered : c8FourActionCovered c8FourRecordData225 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord225_bounded : c8FourActionBounded c8FourRecordData225 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord226_covered : c8FourActionCovered c8FourRecordData226 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord226_bounded : c8FourActionBounded c8FourRecordData226 := by
  decide +kernel

private theorem c8FourActionRecord227_covered : c8FourActionCovered c8FourRecordData227 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord227_bounded : c8FourActionBounded c8FourRecordData227 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord228_covered : c8FourActionCovered c8FourRecordData228 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord228_bounded : c8FourActionBounded c8FourRecordData228 := by
  decide +kernel

private theorem c8FourActionRecord229_covered : c8FourActionCovered c8FourRecordData229 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨53, ?_⟩
  decide +kernel

private theorem c8FourActionRecord229_bounded : c8FourActionBounded c8FourRecordData229 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord230_covered : c8FourActionCovered c8FourRecordData230 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord230_bounded : c8FourActionBounded c8FourRecordData230 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord231_covered : c8FourActionCovered c8FourRecordData231 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord231_bounded : c8FourActionBounded c8FourRecordData231 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord232_covered : c8FourActionCovered c8FourRecordData232 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨7, ?_⟩
  decide +kernel

private theorem c8FourActionRecord232_bounded : c8FourActionBounded c8FourRecordData232 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord233_covered : c8FourActionCovered c8FourRecordData233 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord233_bounded : c8FourActionBounded c8FourRecordData233 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord234_covered : c8FourActionCovered c8FourRecordData234 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord234_bounded : c8FourActionBounded c8FourRecordData234 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord235_covered : c8FourActionCovered c8FourRecordData235 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord235_bounded : c8FourActionBounded c8FourRecordData235 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord236_covered : c8FourActionCovered c8FourRecordData236 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord236_bounded : c8FourActionBounded c8FourRecordData236 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord237_covered : c8FourActionCovered c8FourRecordData237 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord237_bounded : c8FourActionBounded c8FourRecordData237 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord238_covered : c8FourActionCovered c8FourRecordData238 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord238_bounded : c8FourActionBounded c8FourRecordData238 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord239_covered : c8FourActionCovered c8FourRecordData239 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord239_bounded : c8FourActionBounded c8FourRecordData239 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord240_covered : c8FourActionCovered c8FourRecordData240 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord240_bounded : c8FourActionBounded c8FourRecordData240 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord241_covered : c8FourActionCovered c8FourRecordData241 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨6, ?_⟩
  decide +kernel

private theorem c8FourActionRecord241_bounded : c8FourActionBounded c8FourRecordData241 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord242_covered : c8FourActionCovered c8FourRecordData242 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord242_bounded : c8FourActionBounded c8FourRecordData242 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord243_covered : c8FourActionCovered c8FourRecordData243 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord243_bounded : c8FourActionBounded c8FourRecordData243 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord244_covered : c8FourActionCovered c8FourRecordData244 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord244_bounded : c8FourActionBounded c8FourRecordData244 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord245_covered : c8FourActionCovered c8FourRecordData245 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord245_bounded : c8FourActionBounded c8FourRecordData245 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord246_covered : c8FourActionCovered c8FourRecordData246 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord246_bounded : c8FourActionBounded c8FourRecordData246 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord247_covered : c8FourActionCovered c8FourRecordData247 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨49, ?_⟩
  decide +kernel

private theorem c8FourActionRecord247_bounded : c8FourActionBounded c8FourRecordData247 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord248_covered : c8FourActionCovered c8FourRecordData248 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord248_bounded : c8FourActionBounded c8FourRecordData248 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord249_covered : c8FourActionCovered c8FourRecordData249 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨8, ?_⟩
  decide +kernel

private theorem c8FourActionRecord249_bounded : c8FourActionBounded c8FourRecordData249 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord250_covered : c8FourActionCovered c8FourRecordData250 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord250_bounded : c8FourActionBounded c8FourRecordData250 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord251_covered : c8FourActionCovered c8FourRecordData251 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨8, ?_⟩
  decide +kernel

private theorem c8FourActionRecord251_bounded : c8FourActionBounded c8FourRecordData251 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord252_covered : c8FourActionCovered c8FourRecordData252 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨19, ?_⟩
  decide +kernel

private theorem c8FourActionRecord252_bounded : c8FourActionBounded c8FourRecordData252 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord253_covered : c8FourActionCovered c8FourRecordData253 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨20, ?_⟩
  decide +kernel

private theorem c8FourActionRecord253_bounded : c8FourActionBounded c8FourRecordData253 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord254_covered : c8FourActionCovered c8FourRecordData254 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord254_bounded : c8FourActionBounded c8FourRecordData254 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord255_covered : c8FourActionCovered c8FourRecordData255 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord255_bounded : c8FourActionBounded c8FourRecordData255 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionChunk3_covered (j : Fin 64) :
    c8FourActionCovered (c8FourRecordChunk3[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord192_covered
  · exact c8FourActionRecord193_covered
  · exact c8FourActionRecord194_covered
  · exact c8FourActionRecord195_covered
  · exact c8FourActionRecord196_covered
  · exact c8FourActionRecord197_covered
  · exact c8FourActionRecord198_covered
  · exact c8FourActionRecord199_covered
  · exact c8FourActionRecord200_covered
  · exact c8FourActionRecord201_covered
  · exact c8FourActionRecord202_covered
  · exact c8FourActionRecord203_covered
  · exact c8FourActionRecord204_covered
  · exact c8FourActionRecord205_covered
  · exact c8FourActionRecord206_covered
  · exact c8FourActionRecord207_covered
  · exact c8FourActionRecord208_covered
  · exact c8FourActionRecord209_covered
  · exact c8FourActionRecord210_covered
  · exact c8FourActionRecord211_covered
  · exact c8FourActionRecord212_covered
  · exact c8FourActionRecord213_covered
  · exact c8FourActionRecord214_covered
  · exact c8FourActionRecord215_covered
  · exact c8FourActionRecord216_covered
  · exact c8FourActionRecord217_covered
  · exact c8FourActionRecord218_covered
  · exact c8FourActionRecord219_covered
  · exact c8FourActionRecord220_covered
  · exact c8FourActionRecord221_covered
  · exact c8FourActionRecord222_covered
  · exact c8FourActionRecord223_covered
  · exact c8FourActionRecord224_covered
  · exact c8FourActionRecord225_covered
  · exact c8FourActionRecord226_covered
  · exact c8FourActionRecord227_covered
  · exact c8FourActionRecord228_covered
  · exact c8FourActionRecord229_covered
  · exact c8FourActionRecord230_covered
  · exact c8FourActionRecord231_covered
  · exact c8FourActionRecord232_covered
  · exact c8FourActionRecord233_covered
  · exact c8FourActionRecord234_covered
  · exact c8FourActionRecord235_covered
  · exact c8FourActionRecord236_covered
  · exact c8FourActionRecord237_covered
  · exact c8FourActionRecord238_covered
  · exact c8FourActionRecord239_covered
  · exact c8FourActionRecord240_covered
  · exact c8FourActionRecord241_covered
  · exact c8FourActionRecord242_covered
  · exact c8FourActionRecord243_covered
  · exact c8FourActionRecord244_covered
  · exact c8FourActionRecord245_covered
  · exact c8FourActionRecord246_covered
  · exact c8FourActionRecord247_covered
  · exact c8FourActionRecord248_covered
  · exact c8FourActionRecord249_covered
  · exact c8FourActionRecord250_covered
  · exact c8FourActionRecord251_covered
  · exact c8FourActionRecord252_covered
  · exact c8FourActionRecord253_covered
  · exact c8FourActionRecord254_covered
  · exact c8FourActionRecord255_covered

private theorem c8FourActionChunk3_bounded (j : Fin 64) :
    c8FourActionBounded (c8FourRecordChunk3[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord192_bounded
  · exact c8FourActionRecord193_bounded
  · exact c8FourActionRecord194_bounded
  · exact c8FourActionRecord195_bounded
  · exact c8FourActionRecord196_bounded
  · exact c8FourActionRecord197_bounded
  · exact c8FourActionRecord198_bounded
  · exact c8FourActionRecord199_bounded
  · exact c8FourActionRecord200_bounded
  · exact c8FourActionRecord201_bounded
  · exact c8FourActionRecord202_bounded
  · exact c8FourActionRecord203_bounded
  · exact c8FourActionRecord204_bounded
  · exact c8FourActionRecord205_bounded
  · exact c8FourActionRecord206_bounded
  · exact c8FourActionRecord207_bounded
  · exact c8FourActionRecord208_bounded
  · exact c8FourActionRecord209_bounded
  · exact c8FourActionRecord210_bounded
  · exact c8FourActionRecord211_bounded
  · exact c8FourActionRecord212_bounded
  · exact c8FourActionRecord213_bounded
  · exact c8FourActionRecord214_bounded
  · exact c8FourActionRecord215_bounded
  · exact c8FourActionRecord216_bounded
  · exact c8FourActionRecord217_bounded
  · exact c8FourActionRecord218_bounded
  · exact c8FourActionRecord219_bounded
  · exact c8FourActionRecord220_bounded
  · exact c8FourActionRecord221_bounded
  · exact c8FourActionRecord222_bounded
  · exact c8FourActionRecord223_bounded
  · exact c8FourActionRecord224_bounded
  · exact c8FourActionRecord225_bounded
  · exact c8FourActionRecord226_bounded
  · exact c8FourActionRecord227_bounded
  · exact c8FourActionRecord228_bounded
  · exact c8FourActionRecord229_bounded
  · exact c8FourActionRecord230_bounded
  · exact c8FourActionRecord231_bounded
  · exact c8FourActionRecord232_bounded
  · exact c8FourActionRecord233_bounded
  · exact c8FourActionRecord234_bounded
  · exact c8FourActionRecord235_bounded
  · exact c8FourActionRecord236_bounded
  · exact c8FourActionRecord237_bounded
  · exact c8FourActionRecord238_bounded
  · exact c8FourActionRecord239_bounded
  · exact c8FourActionRecord240_bounded
  · exact c8FourActionRecord241_bounded
  · exact c8FourActionRecord242_bounded
  · exact c8FourActionRecord243_bounded
  · exact c8FourActionRecord244_bounded
  · exact c8FourActionRecord245_bounded
  · exact c8FourActionRecord246_bounded
  · exact c8FourActionRecord247_bounded
  · exact c8FourActionRecord248_bounded
  · exact c8FourActionRecord249_bounded
  · exact c8FourActionRecord250_bounded
  · exact c8FourActionRecord251_bounded
  · exact c8FourActionRecord252_bounded
  · exact c8FourActionRecord253_bounded
  · exact c8FourActionRecord254_bounded
  · exact c8FourActionRecord255_bounded

end CertificateChecks.Batch103

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers in
theorem certificate103 : (c8FourActionCovered c8FourRecordData192)
    ∧ (c8FourActionBounded c8FourRecordData192)
    ∧ (c8FourActionCovered c8FourRecordData193)
    ∧ (c8FourActionBounded c8FourRecordData193)
    ∧ (c8FourActionCovered c8FourRecordData194)
    ∧ (c8FourActionBounded c8FourRecordData194)
    ∧ (c8FourActionCovered c8FourRecordData195)
    ∧ (c8FourActionBounded c8FourRecordData195)
    ∧ (c8FourActionCovered c8FourRecordData196)
    ∧ (c8FourActionBounded c8FourRecordData196)
    ∧ (c8FourActionCovered c8FourRecordData197)
    ∧ (c8FourActionBounded c8FourRecordData197)
    ∧ (c8FourActionCovered c8FourRecordData198)
    ∧ (c8FourActionBounded c8FourRecordData198)
    ∧ (c8FourActionCovered c8FourRecordData199)
    ∧ (c8FourActionBounded c8FourRecordData199)
    ∧ (c8FourActionCovered c8FourRecordData200)
    ∧ (c8FourActionBounded c8FourRecordData200)
    ∧ (c8FourActionCovered c8FourRecordData201)
    ∧ (c8FourActionBounded c8FourRecordData201)
    ∧ (c8FourActionCovered c8FourRecordData202)
    ∧ (c8FourActionBounded c8FourRecordData202)
    ∧ (c8FourActionCovered c8FourRecordData203)
    ∧ (c8FourActionBounded c8FourRecordData203)
    ∧ (c8FourActionCovered c8FourRecordData204)
    ∧ (c8FourActionBounded c8FourRecordData204)
    ∧ (c8FourActionCovered c8FourRecordData205)
    ∧ (c8FourActionBounded c8FourRecordData205)
    ∧ (c8FourActionCovered c8FourRecordData206)
    ∧ (c8FourActionBounded c8FourRecordData206)
    ∧ (c8FourActionCovered c8FourRecordData207)
    ∧ (c8FourActionBounded c8FourRecordData207)
    ∧ (c8FourActionCovered c8FourRecordData208)
    ∧ (c8FourActionBounded c8FourRecordData208)
    ∧ (c8FourActionCovered c8FourRecordData209)
    ∧ (c8FourActionBounded c8FourRecordData209)
    ∧ (c8FourActionCovered c8FourRecordData210)
    ∧ (c8FourActionBounded c8FourRecordData210)
    ∧ (c8FourActionCovered c8FourRecordData211)
    ∧ (c8FourActionBounded c8FourRecordData211)
    ∧ (c8FourActionCovered c8FourRecordData212)
    ∧ (c8FourActionBounded c8FourRecordData212)
    ∧ (c8FourActionCovered c8FourRecordData213)
    ∧ (c8FourActionBounded c8FourRecordData213)
    ∧ (c8FourActionCovered c8FourRecordData214)
    ∧ (c8FourActionBounded c8FourRecordData214)
    ∧ (c8FourActionCovered c8FourRecordData215)
    ∧ (c8FourActionBounded c8FourRecordData215)
    ∧ (c8FourActionCovered c8FourRecordData216)
    ∧ (c8FourActionBounded c8FourRecordData216)
    ∧ (c8FourActionCovered c8FourRecordData217)
    ∧ (c8FourActionBounded c8FourRecordData217)
    ∧ (c8FourActionCovered c8FourRecordData218)
    ∧ (c8FourActionBounded c8FourRecordData218)
    ∧ (c8FourActionCovered c8FourRecordData219)
    ∧ (c8FourActionBounded c8FourRecordData219)
    ∧ (c8FourActionCovered c8FourRecordData220)
    ∧ (c8FourActionBounded c8FourRecordData220)
    ∧ (c8FourActionCovered c8FourRecordData221)
    ∧ (c8FourActionBounded c8FourRecordData221)
    ∧ (c8FourActionCovered c8FourRecordData222)
    ∧ (c8FourActionBounded c8FourRecordData222)
    ∧ (c8FourActionCovered c8FourRecordData223)
    ∧ (c8FourActionBounded c8FourRecordData223)
    ∧ (c8FourActionCovered c8FourRecordData224)
    ∧ (c8FourActionBounded c8FourRecordData224)
    ∧ (c8FourActionCovered c8FourRecordData225)
    ∧ (c8FourActionBounded c8FourRecordData225)
    ∧ (c8FourActionCovered c8FourRecordData226)
    ∧ (c8FourActionBounded c8FourRecordData226)
    ∧ (c8FourActionCovered c8FourRecordData227)
    ∧ (c8FourActionBounded c8FourRecordData227)
    ∧ (c8FourActionCovered c8FourRecordData228)
    ∧ (c8FourActionBounded c8FourRecordData228)
    ∧ (c8FourActionCovered c8FourRecordData229)
    ∧ (c8FourActionBounded c8FourRecordData229)
    ∧ (c8FourActionCovered c8FourRecordData230)
    ∧ (c8FourActionBounded c8FourRecordData230)
    ∧ (c8FourActionCovered c8FourRecordData231)
    ∧ (c8FourActionBounded c8FourRecordData231)
    ∧ (c8FourActionCovered c8FourRecordData232)
    ∧ (c8FourActionBounded c8FourRecordData232)
    ∧ (c8FourActionCovered c8FourRecordData233)
    ∧ (c8FourActionBounded c8FourRecordData233)
    ∧ (c8FourActionCovered c8FourRecordData234)
    ∧ (c8FourActionBounded c8FourRecordData234)
    ∧ (c8FourActionCovered c8FourRecordData235)
    ∧ (c8FourActionBounded c8FourRecordData235)
    ∧ (c8FourActionCovered c8FourRecordData236)
    ∧ (c8FourActionBounded c8FourRecordData236)
    ∧ (c8FourActionCovered c8FourRecordData237)
    ∧ (c8FourActionBounded c8FourRecordData237)
    ∧ (c8FourActionCovered c8FourRecordData238)
    ∧ (c8FourActionBounded c8FourRecordData238)
    ∧ (c8FourActionCovered c8FourRecordData239)
    ∧ (c8FourActionBounded c8FourRecordData239)
    ∧ (c8FourActionCovered c8FourRecordData240)
    ∧ (c8FourActionBounded c8FourRecordData240)
    ∧ (c8FourActionCovered c8FourRecordData241)
    ∧ (c8FourActionBounded c8FourRecordData241)
    ∧ (c8FourActionCovered c8FourRecordData242)
    ∧ (c8FourActionBounded c8FourRecordData242)
    ∧ (c8FourActionCovered c8FourRecordData243)
    ∧ (c8FourActionBounded c8FourRecordData243)
    ∧ (c8FourActionCovered c8FourRecordData244)
    ∧ (c8FourActionBounded c8FourRecordData244)
    ∧ (c8FourActionCovered c8FourRecordData245)
    ∧ (c8FourActionBounded c8FourRecordData245)
    ∧ (c8FourActionCovered c8FourRecordData246)
    ∧ (c8FourActionBounded c8FourRecordData246)
    ∧ (c8FourActionCovered c8FourRecordData247)
    ∧ (c8FourActionBounded c8FourRecordData247)
    ∧ (c8FourActionCovered c8FourRecordData248)
    ∧ (c8FourActionBounded c8FourRecordData248)
    ∧ (c8FourActionCovered c8FourRecordData249)
    ∧ (c8FourActionBounded c8FourRecordData249)
    ∧ (c8FourActionCovered c8FourRecordData250)
    ∧ (c8FourActionBounded c8FourRecordData250)
    ∧ (c8FourActionCovered c8FourRecordData251)
    ∧ (c8FourActionBounded c8FourRecordData251)
    ∧ (c8FourActionCovered c8FourRecordData252)
    ∧ (c8FourActionBounded c8FourRecordData252)
    ∧ (c8FourActionCovered c8FourRecordData253)
    ∧ (c8FourActionBounded c8FourRecordData253)
    ∧ (c8FourActionCovered c8FourRecordData254)
    ∧ (c8FourActionBounded c8FourRecordData254)
    ∧ (c8FourActionCovered c8FourRecordData255)
    ∧ (c8FourActionBounded c8FourRecordData255) := by
  exact ⟨CertificateChecks.Batch103.c8FourActionRecord192_covered, CertificateChecks.Batch103.c8FourActionRecord192_bounded, CertificateChecks.Batch103.c8FourActionRecord193_covered, CertificateChecks.Batch103.c8FourActionRecord193_bounded, CertificateChecks.Batch103.c8FourActionRecord194_covered, CertificateChecks.Batch103.c8FourActionRecord194_bounded, CertificateChecks.Batch103.c8FourActionRecord195_covered, CertificateChecks.Batch103.c8FourActionRecord195_bounded, CertificateChecks.Batch103.c8FourActionRecord196_covered, CertificateChecks.Batch103.c8FourActionRecord196_bounded, CertificateChecks.Batch103.c8FourActionRecord197_covered, CertificateChecks.Batch103.c8FourActionRecord197_bounded, CertificateChecks.Batch103.c8FourActionRecord198_covered, CertificateChecks.Batch103.c8FourActionRecord198_bounded, CertificateChecks.Batch103.c8FourActionRecord199_covered, CertificateChecks.Batch103.c8FourActionRecord199_bounded, CertificateChecks.Batch103.c8FourActionRecord200_covered, CertificateChecks.Batch103.c8FourActionRecord200_bounded, CertificateChecks.Batch103.c8FourActionRecord201_covered, CertificateChecks.Batch103.c8FourActionRecord201_bounded, CertificateChecks.Batch103.c8FourActionRecord202_covered, CertificateChecks.Batch103.c8FourActionRecord202_bounded, CertificateChecks.Batch103.c8FourActionRecord203_covered, CertificateChecks.Batch103.c8FourActionRecord203_bounded, CertificateChecks.Batch103.c8FourActionRecord204_covered, CertificateChecks.Batch103.c8FourActionRecord204_bounded, CertificateChecks.Batch103.c8FourActionRecord205_covered, CertificateChecks.Batch103.c8FourActionRecord205_bounded, CertificateChecks.Batch103.c8FourActionRecord206_covered, CertificateChecks.Batch103.c8FourActionRecord206_bounded, CertificateChecks.Batch103.c8FourActionRecord207_covered, CertificateChecks.Batch103.c8FourActionRecord207_bounded, CertificateChecks.Batch103.c8FourActionRecord208_covered, CertificateChecks.Batch103.c8FourActionRecord208_bounded, CertificateChecks.Batch103.c8FourActionRecord209_covered, CertificateChecks.Batch103.c8FourActionRecord209_bounded, CertificateChecks.Batch103.c8FourActionRecord210_covered, CertificateChecks.Batch103.c8FourActionRecord210_bounded, CertificateChecks.Batch103.c8FourActionRecord211_covered, CertificateChecks.Batch103.c8FourActionRecord211_bounded, CertificateChecks.Batch103.c8FourActionRecord212_covered, CertificateChecks.Batch103.c8FourActionRecord212_bounded, CertificateChecks.Batch103.c8FourActionRecord213_covered, CertificateChecks.Batch103.c8FourActionRecord213_bounded, CertificateChecks.Batch103.c8FourActionRecord214_covered, CertificateChecks.Batch103.c8FourActionRecord214_bounded, CertificateChecks.Batch103.c8FourActionRecord215_covered, CertificateChecks.Batch103.c8FourActionRecord215_bounded, CertificateChecks.Batch103.c8FourActionRecord216_covered, CertificateChecks.Batch103.c8FourActionRecord216_bounded, CertificateChecks.Batch103.c8FourActionRecord217_covered, CertificateChecks.Batch103.c8FourActionRecord217_bounded, CertificateChecks.Batch103.c8FourActionRecord218_covered, CertificateChecks.Batch103.c8FourActionRecord218_bounded, CertificateChecks.Batch103.c8FourActionRecord219_covered, CertificateChecks.Batch103.c8FourActionRecord219_bounded, CertificateChecks.Batch103.c8FourActionRecord220_covered, CertificateChecks.Batch103.c8FourActionRecord220_bounded, CertificateChecks.Batch103.c8FourActionRecord221_covered, CertificateChecks.Batch103.c8FourActionRecord221_bounded, CertificateChecks.Batch103.c8FourActionRecord222_covered, CertificateChecks.Batch103.c8FourActionRecord222_bounded, CertificateChecks.Batch103.c8FourActionRecord223_covered, CertificateChecks.Batch103.c8FourActionRecord223_bounded, CertificateChecks.Batch103.c8FourActionRecord224_covered, CertificateChecks.Batch103.c8FourActionRecord224_bounded, CertificateChecks.Batch103.c8FourActionRecord225_covered, CertificateChecks.Batch103.c8FourActionRecord225_bounded, CertificateChecks.Batch103.c8FourActionRecord226_covered, CertificateChecks.Batch103.c8FourActionRecord226_bounded, CertificateChecks.Batch103.c8FourActionRecord227_covered, CertificateChecks.Batch103.c8FourActionRecord227_bounded, CertificateChecks.Batch103.c8FourActionRecord228_covered, CertificateChecks.Batch103.c8FourActionRecord228_bounded, CertificateChecks.Batch103.c8FourActionRecord229_covered, CertificateChecks.Batch103.c8FourActionRecord229_bounded, CertificateChecks.Batch103.c8FourActionRecord230_covered, CertificateChecks.Batch103.c8FourActionRecord230_bounded, CertificateChecks.Batch103.c8FourActionRecord231_covered, CertificateChecks.Batch103.c8FourActionRecord231_bounded, CertificateChecks.Batch103.c8FourActionRecord232_covered, CertificateChecks.Batch103.c8FourActionRecord232_bounded, CertificateChecks.Batch103.c8FourActionRecord233_covered, CertificateChecks.Batch103.c8FourActionRecord233_bounded, CertificateChecks.Batch103.c8FourActionRecord234_covered, CertificateChecks.Batch103.c8FourActionRecord234_bounded, CertificateChecks.Batch103.c8FourActionRecord235_covered, CertificateChecks.Batch103.c8FourActionRecord235_bounded, CertificateChecks.Batch103.c8FourActionRecord236_covered, CertificateChecks.Batch103.c8FourActionRecord236_bounded, CertificateChecks.Batch103.c8FourActionRecord237_covered, CertificateChecks.Batch103.c8FourActionRecord237_bounded, CertificateChecks.Batch103.c8FourActionRecord238_covered, CertificateChecks.Batch103.c8FourActionRecord238_bounded, CertificateChecks.Batch103.c8FourActionRecord239_covered, CertificateChecks.Batch103.c8FourActionRecord239_bounded, CertificateChecks.Batch103.c8FourActionRecord240_covered, CertificateChecks.Batch103.c8FourActionRecord240_bounded, CertificateChecks.Batch103.c8FourActionRecord241_covered, CertificateChecks.Batch103.c8FourActionRecord241_bounded, CertificateChecks.Batch103.c8FourActionRecord242_covered, CertificateChecks.Batch103.c8FourActionRecord242_bounded, CertificateChecks.Batch103.c8FourActionRecord243_covered, CertificateChecks.Batch103.c8FourActionRecord243_bounded, CertificateChecks.Batch103.c8FourActionRecord244_covered, CertificateChecks.Batch103.c8FourActionRecord244_bounded, CertificateChecks.Batch103.c8FourActionRecord245_covered, CertificateChecks.Batch103.c8FourActionRecord245_bounded, CertificateChecks.Batch103.c8FourActionRecord246_covered, CertificateChecks.Batch103.c8FourActionRecord246_bounded, CertificateChecks.Batch103.c8FourActionRecord247_covered, CertificateChecks.Batch103.c8FourActionRecord247_bounded, CertificateChecks.Batch103.c8FourActionRecord248_covered, CertificateChecks.Batch103.c8FourActionRecord248_bounded, CertificateChecks.Batch103.c8FourActionRecord249_covered, CertificateChecks.Batch103.c8FourActionRecord249_bounded, CertificateChecks.Batch103.c8FourActionRecord250_covered, CertificateChecks.Batch103.c8FourActionRecord250_bounded, CertificateChecks.Batch103.c8FourActionRecord251_covered, CertificateChecks.Batch103.c8FourActionRecord251_bounded, CertificateChecks.Batch103.c8FourActionRecord252_covered, CertificateChecks.Batch103.c8FourActionRecord252_bounded, CertificateChecks.Batch103.c8FourActionRecord253_covered, CertificateChecks.Batch103.c8FourActionRecord253_bounded, CertificateChecks.Batch103.c8FourActionRecord254_covered, CertificateChecks.Batch103.c8FourActionRecord254_bounded, CertificateChecks.Batch103.c8FourActionRecord255_covered, CertificateChecks.Batch103.c8FourActionRecord255_bounded⟩

end Certificates
