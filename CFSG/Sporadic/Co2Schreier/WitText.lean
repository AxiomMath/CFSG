module

public import CFSG.Sporadic.Co2Schreier.WitLit

public section

namespace CFSG.Sporadic.Co2Schreier

open Lean (Json)
open CFSG.Monster.B.Mathieu

@[expose] def witText : String := include_str "Data"/"full-centralizer-witnesses.txt"

@[expose] def WitLocal.ofJson (j : Json) : Except String WitLocal := do
  pure
    { sixAnchor := ← j.getObjValAs? ℕ "six_anchor"
      sixBasisIndices := ← j.getObjValAs? (List ℕ) "six_basis_indices"
      sixGramRows := ← j.getObjValAs? (List ℕ) "six_gram_rows"
      sixRows := ← j.getObjValAs? (List (List ℕ)) "six_rows"
      sixActionChain := ← ChainRecord.ofJson (← j.getObjVal? "six_action_chain")
      qQuotientBasisIndices := ← j.getObjValAs? (List ℕ) "Q_quotient_basis_indices"
      qQuotientActionRows := ← j.getObjValAs? (List (List ℕ)) "Q_quotient_action_rows"
      dStrongFixedBySIndices := ← j.getObjValAs? (List ℕ) "D_strong_fixed_by_S_indices"
      dCandidateSurvivors := ← j.getObjValAs? (List (List ℕ)) "D_candidate_survivors"
      dAdditionalFixedWords := ← j.getObjValAs? (List (List ℤ)) "D_additional_fixed_words"
      dInnerSurvivors := ← j.getObjValAs? (List (List ℕ)) "D_inner_survivors" }

@[expose] def WitRep.ofJson (j : Json) : Except String WitRep := do
  pure
    { sylowIndex := ← j.getObjValAs? ℕ "sylow_index"
      rankMinusIdentity := ← j.getObjValAs? ℕ "rank_minus_identity"
      matrixRows := ← j.getObjValAs? (List ℕ) "matrix_rows" }

@[expose] def WitBatch.ofJson (j : Json) : Except String WitBatch := do
  pure
    { representative := ← j.getObjValAs? ℕ "representative"
      conjugatingWord := ← j.getObjValAs? (List ℤ) "conjugating_word"
      pairs := ← j.getObjValAs? (List (List ℕ)) "matches" }

@[expose] def WitFusion.ofJson (j : Json) : Except String WitFusion := do
  let reps ← (← (← j.getObjVal? "representatives").getArr?).toList.mapM WitRep.ofJson
  let bs ← (← (← j.getObjVal? "fusion_batches").getArr?).toList.mapM WitBatch.ofJson
  pure
    { sylowOrder := ← j.getObjValAs? ℕ "sylow_order"
      representatives := reps
      rankCounts := ← j.getObjValAs? (List (List ℕ)) "rank_counts"
      fusionBatches := bs }

@[expose] def WitObstruction.ofJson (j : Json) : Except String WitObstruction := do
  pure
    { prime := ← j.getObjValAs? ℕ "prime"
      element := ← j.getObjValAs? (List ℕ) "element"
      conjugator := ← j.getObjValAs? (List ℕ) "conjugator" }

@[expose] def WitOdd.ofJson (j : Json) : Except String WitOdd := do
  let obs ← (← (← j.getObjVal? "obstructions").getArr?).toList.mapM WitObstruction.ofJson
  pure
    { sylowThreeGenerators := ← j.getObjValAs? (List (List ℕ)) "sylow_three_generators"
      sylowFiveGenerator := ← j.getObjValAs? (List ℕ) "sylow_five_generator"
      obstructions := obs }

@[expose] def WitThird.ofJson (j : Json) : Except String WitThird := do
  pure
    { baseIndices := ← j.getObjValAs? (List ℕ) "base_indices"
      strongDerivations := ← j.getObjValAs? (List (List ℤ)) "strong_derivations"
      fixedPoints := ← j.getObjValAs? (List ℕ) "fixed_points"
      fixedBasis := ← j.getObjValAs? (List ℕ) "fixed_basis"
      odd := ← WitOdd.ofJson (← j.getObjVal? "odd") }

@[expose] def WitCert.ofJson (j : Json) : Except String WitCert := do
  pure
    { wLocal := ← WitLocal.ofJson (← j.getObjVal? "local")
      fusion := ← WitFusion.ofJson (← j.getObjVal? "fusion")
      third := ← WitThird.ofJson (← j.getObjVal? "third") }

@[expose] def witKeysAt (path : List String) : Except String (List String) := do
  let mut j ← Json.parse witText
  for k in path do
    j ← j.getObjVal? k
  let o ← j.getObj?
  pure (o.toArray.map (·.1)).toList

@[expose] def witFile : Except String WitCert := do
  WitCert.ofJson (← Json.parse witText)

@[expose] def witRec : WitCert := witRecLit

end CFSG.Sporadic.Co2Schreier
