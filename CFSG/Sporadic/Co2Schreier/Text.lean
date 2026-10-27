module

public import CFSG.Sporadic.Co2Schreier.LocalLit

public section

namespace CFSG.Sporadic.Co2Schreier

open Lean (Json)
open CFSG.Monster.B.Mathieu

@[expose] def localText : String := include_str "Data"/"local-certificate.txt"

@[expose] def LocalChains.ofJson (j : Json) : Except String LocalChains := do
  pure
    { C := ← ChainRecord.ofJson (← j.getObjVal? "C")
      D := ← ChainRecord.ofJson (← j.getObjVal? "D")
      qAction := ← ChainRecord.ofJson (← j.getObjVal? "Q_action")
      rAction := ← ChainRecord.ofJson (← j.getObjVal? "R_action")
      S := ← ChainRecord.ofJson (← j.getObjVal? "S")
      join := ← ChainRecord.ofJson (← j.getObjVal? "join") }

@[expose] def LocalCert.ofJson (j : Json) : Except String LocalCert := do
  pure
    { cInitialCenterWord := ← j.getObjValAs? (List ℤ) "C_initial_center_word"
      cInitialWords := ← j.getObjValAs? (List (List ℤ)) "C_initial_words"
      cStrongDerivations := ← j.getObjValAs? (List (List ℤ)) "C_strong_derivations"
      dCenterWord := ← j.getObjValAs? (List ℤ) "D_center_word"
      dStrongDerivations := ← j.getObjValAs? (List (List ℤ)) "D_strong_derivations"
      dWords := ← j.getObjValAs? (List (List ℤ)) "D_words"
      frattiniProfiles := ← j.getObjValAs? (List (List ℕ)) "Frattini_profiles"
      qWords := ← j.getObjValAs? (List (List ℤ)) "Q_words"
      rWords := ← j.getObjValAs? (List (List ℤ)) "R_words"
      sQuotientWords := ← j.getObjValAs? (List (List ℤ)) "S_quotient_words"
      alignmentIntermediateWord := ← j.getObjValAs? (List ℤ) "alignment_intermediate_word"
      alignmentOddOrders := ← j.getObjValAs? (List ℕ) "alignment_odd_orders"
      chains := ← LocalChains.ofJson (← j.getObjVal? "chains")
      expectedFrattiniRank := ← j.getObjValAs? ℕ "expected_Frattini_rank"
      expectedCentralizerIndices := ← j.getObjValAs? (List ℕ) "expected_centralizer_indices"
      schemaVersion := ← j.getObjValAs? ℕ "schema_version"
      zRWord := ← j.getObjValAs? (List ℤ) "z_R_word" }

@[expose] def localKeys : Except String (List String) := do
  let o ← (← Json.parse localText).getObj?
  pure (o.toArray.map (·.1)).toList

@[expose] def localChainKeys : Except String (List String) := do
  let o ← ((← (← Json.parse localText).getObjVal? "chains")).getObj?
  pure (o.toArray.map (·.1)).toList

@[expose] def localFile : Except String LocalCert := do
  LocalCert.ofJson (← Json.parse localText)

@[expose] def localRec : LocalCert := localRecLit

end CFSG.Sporadic.Co2Schreier
