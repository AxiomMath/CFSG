module

public import CFSG.Sporadic.Schreier.J1CertLit

public section

namespace CFSG.Sporadic.Schreier

open Lean (Json)
open CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2.Native

@[expose] def j1CertificateText : String := include_str "Data" / "j1-simplicity-certificate.json"

@[expose] def J1CertificateFile.ofJson (j : Json) : Except String J1CertificateFile := do
  let sy ← (← (← j.getObjVal? "sylows").getArr?).toList.mapM SylowRecord.ofJson
  pure
    { schemaVersion := ← j.getObjValAs? ℕ "schema_version"
      group := ← j.getObjValAs? String "group"
      prime := ← j.getObjValAs? ℕ "prime"
      dimension := ← j.getObjValAs? ℕ "dimension"
      vectors := ← j.getObjValAs? (List (List ℕ)) "vectors"
      basisIndices := ← j.getObjValAs? (List ℕ) "basis_indices"
      chain := ← ChainRecord.ofJson (← j.getObjVal? "chain")
      sylows := sy }

@[expose] def j1CertificateFile : Except String J1CertificateFile := do
  J1CertificateFile.ofJson (← Json.parse j1CertificateText)

@[expose, irreducible] def J1Certificate : J1CertificateFile :=
  Function.const _ j1CertLit j1CertificateFile

@[expose] def isPermList (n : ℕ) (a : List ℕ) : Bool :=
  a.length == n && isInvA n a.toArray (invCand n a.toArray)

@[expose] def j1Vec (i : Fin 3080) : Fin 7 → ZMod 11 :=
  fun j => (((J1Certificate.vectors.getD i []).getD j 0 : ℕ) : ZMod 11)

@[expose] def j1A1List : List ℕ := J1Certificate.chain.generators.getD 0 []

@[expose] def j1A2List : List ℕ := J1Certificate.chain.generators.getD 1 []

@[expose] noncomputable def j1A1 : Equiv.Perm (Fin 3080) := arrPerm 3080 j1A1List

@[expose] noncomputable def j1A2 : Equiv.Perm (Fin 3080) := arrPerm 3080 j1A2List

@[expose] noncomputable def j1P : Subgroup (Equiv.Perm (Fin 3080)) :=
  Subgroup.closure {j1A1, j1A2}

end CFSG.Sporadic.Schreier
