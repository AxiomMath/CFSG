module

public import CFSG.Sporadic.Co2Cert.Text0
public import CFSG.Sporadic.Co2Cert.Text1
public import CFSG.Sporadic.Co2Cert.Text2
public import CFSG.Sporadic.Co2Cert.Text3
public import CFSG.Sporadic.Co2Cert.Text4
public import CFSG.Sporadic.Co2Cert.Text5
public import CFSG.Sporadic.Co2Cert.Lit
public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.Sporadic.Co2Cert

open Lean (Json)
open CFSG.Monster.B.Mathieu

@[expose] def co2CertText : String :=
  co2Text0 ++ co2Text1 ++ co2Text2 ++ co2Text3 ++ co2Text4 ++ co2Text5

@[expose] def Co2Merge.ofJson (j : Json) : Except String Co2Merge := do
  pure
    { representative := ← j.getObjValAs? ℕ "representative"
      instructions := ← j.getObjValAs? (List (List ℕ)) "instructions" }

@[expose] def Co2CertFile.ofJson (j : Json) : Except String Co2CertFile := do
  let ms ← (← (← j.getObjVal? "merges").getArr?).toList.mapM Co2Merge.ofJson
  pure
    { schemaVersion := ← j.getObjValAs? ℕ "schema_version"
      group := ← j.getObjValAs? String "group"
      prime := ← j.getObjValAs? ℕ "prime"
      dimension := ← j.getObjValAs? ℕ "dimension"
      vectors := ← j.getObjValAs? (List (List ℕ)) "vectors"
      basisIndices := ← j.getObjValAs? (List ℕ) "basis_indices"
      chain := ← ChainRecord.ofJson (← j.getObjVal? "chain")
      coprimeConjugator := ← j.getObjValAs? (List ℤ) "coprime_conjugator"
      coprimeChain := ← ChainRecord.ofJson (← j.getObjVal? "coprime_chain")
      point := ← j.getObjValAs? ℕ "point"
      stabilizerGeneratorIndices := ← j.getObjValAs? (List ℕ) "stabilizer_generator_indices"
      stabilizerOrbits := ← j.getObjValAs? (List (List ℕ)) "stabilizer_orbits"
      merges := ms }

@[expose] def co2CertKeys : Except String (List String) := do
  let o ← (← Json.parse co2CertText).getObj?
  pure (o.toArray.map (·.1)).toList

@[expose] def co2CertFile : Except String Co2CertFile := do
  Co2CertFile.ofJson (← Json.parse co2CertText)

@[expose, irreducible] def co2Rec : Co2CertFile := Function.const _ co2RecLit co2CertFile

@[expose] def packVec (l : List ℕ) : ℕ :=
  CFSG.Sporadic.SmallF2.Native.ofBits 22 fun j => l.getD j 0 % 2 == 1

@[expose] def co2PackedVecs : Array ℕ := (co2Rec.vectors.map packVec).toArray

@[expose] def co2OrigArrs : Array (Array ℕ) := co2Rec.chain.origArrs

@[expose] def co2StrongArrs : Array (Array ℕ) := co2Rec.chain.strongArrs

@[expose] def co2BaseArr : Array ℕ := co2Rec.chain.baseArr

@[expose] def co2WordArrs : Array (List ℤ) := co2Rec.chain.wordArrs

@[expose] def co2cOrigArrs : Array (Array ℕ) := co2Rec.coprimeChain.origArrs

@[expose] def co2cStrongArrs : Array (Array ℕ) := co2Rec.coprimeChain.strongArrs

@[expose] def co2cBaseArr : Array ℕ := co2Rec.coprimeChain.baseArr

@[expose] def co2cWordArrs : Array (List ℤ) := co2Rec.coprimeChain.wordArrs

end CFSG.Sporadic.Co2Cert
