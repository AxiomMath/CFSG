module

public import CFSG.Sporadic.Schreier.Co1CertText0
public import CFSG.Sporadic.Schreier.Co1CertText1
public import CFSG.Sporadic.Schreier.Co1CertText2
public import CFSG.Sporadic.Schreier.Co1CertText3
public import CFSG.Sporadic.Schreier.Co1CertText4
public import CFSG.Sporadic.Schreier.Co1CertText5
public import CFSG.Sporadic.Schreier.Co1CertText6
public import CFSG.Sporadic.Schreier.Co1CertText7
public import CFSG.Sporadic.Schreier.Co1CertRecData
public import CFSG.Sporadic.Schreier.Co1StabData
public import CFSG.Sporadic.Schreier.Co1QuotData
public import CFSG.Sporadic.Schreier.Co1LiftData
public import CFSG.Sporadic.Co1Block.PermData
public import Lean.Data.Json.FromToJson.Basic
public import Lean.Data.Json.Parser

public section

namespace CFSG.Sporadic.Co1Schreier

open Lean (Json)

@[expose] def co1CertText : String :=
  co1CertText0 ++ co1CertText1 ++ co1CertText2 ++ co1CertText3 ++ co1CertText4 ++
    co1CertText5 ++ co1CertText6 ++ co1CertText7

structure Co1Merge where
  representative : Nat
  instructions : List (List Nat)
  deriving DecidableEq, Inhabited

structure Co1CertFile where
  schemaVersion : Nat
  group : String
  prime : Nat
  dimension : Nat
  vectors : List Nat
  generatorActions : List (List Nat)
  basisIndices : List Nat
  subgroupWords : List (List Nat)
  subgroupMatrixRows : List (List Nat)
  quotientFixedVector : Nat
  quotientRepresentatives : List Nat
  quotientActions : List (List Nat)
  point : Nat
  stabilizerOrbits : List (List Nat)
  merges : List Co1Merge
  deriving DecidableEq, Inhabited

@[expose] def Co1Merge.ofJson (j : Json) : Except String Co1Merge := do
  pure
    { representative := ← j.getObjValAs? Nat "representative"
      instructions := ← j.getObjValAs? (List (List Nat)) "instructions" }

@[expose] def Co1CertFile.ofJson (j : Json) : Except String Co1CertFile := do
  let ms ← (← (← j.getObjVal? "merges").getArr?).toList.mapM Co1Merge.ofJson
  pure
    { schemaVersion := ← j.getObjValAs? Nat "schema_version"
      group := ← j.getObjValAs? String "group"
      prime := ← j.getObjValAs? Nat "prime"
      dimension := ← j.getObjValAs? Nat "dimension"
      vectors := ← j.getObjValAs? (List Nat) "vectors"
      generatorActions := ← j.getObjValAs? (List (List Nat)) "generator_actions"
      basisIndices := ← j.getObjValAs? (List Nat) "basis_indices"
      subgroupWords := ← j.getObjValAs? (List (List Nat)) "subgroup_words"
      subgroupMatrixRows := ← j.getObjValAs? (List (List Nat)) "subgroup_matrix_rows"
      quotientFixedVector := ← j.getObjValAs? Nat "quotient_fixed_vector"
      quotientRepresentatives := ← j.getObjValAs? (List Nat) "quotient_representatives"
      quotientActions := ← j.getObjValAs? (List (List Nat)) "quotient_actions"
      point := ← j.getObjValAs? Nat "point"
      stabilizerOrbits := ← j.getObjValAs? (List (List Nat)) "stabilizer_orbits"
      merges := ms }

@[expose] def co1CertKeys : Except String (List String) := do
  let o ← (← Json.parse co1CertText).getObj?
  pure (o.toArray.map (·.1)).toList

@[expose] def co1CertFile : Except String Co1CertFile := do
  Co1CertFile.ofJson (← Json.parse co1CertText)

@[expose] noncomputable def co1Rec : Co1CertFile where
  schemaVersion := 1
  group := "Co1"
  prime := 2
  dimension := 24
  vectors := CFSG.Sporadic.Co1Block.certVecs.toList
  generatorActions :=
    [(CFSG.Sporadic.Co1Block.certAct 0).toList, (CFSG.Sporadic.Co1Block.certAct 1).toList]
  basisIndices := CFSG.Sporadic.Co1Block.certBasisIdx
  subgroupWords := [Data.stabWord0, Data.stabWord1]
  subgroupMatrixRows := [Data.subRows0, Data.subRows1]
  quotientFixedVector := Data.quotFixed
  quotientRepresentatives := Data.liftReps
  quotientActions := [Data.quotAct0, Data.quotAct1]
  point := 0
  stabilizerOrbits := [RecData.o0, RecData.o1, RecData.o2, RecData.o3]
  merges :=
    [⟨1, RecData.m0.map RecData.triple⟩, ⟨3, RecData.m1.map RecData.triple⟩,
      ⟨61, RecData.m2.map RecData.triple⟩]

@[expose] noncomputable def certVecArr : Array Nat := co1Rec.vectors.toArray

@[expose] noncomputable def certActArr (k : Nat) : Array Nat :=
  (co1Rec.generatorActions.getD k []).toArray

theorem co1Rec_vectors : co1Rec.vectors = CFSG.Sporadic.Co1Block.certVecs.toList := rfl

theorem co1Rec_generatorActions : co1Rec.generatorActions =
    [(CFSG.Sporadic.Co1Block.certAct 0).toList, (CFSG.Sporadic.Co1Block.certAct 1).toList] := rfl

theorem co1Rec_stabilizerOrbits :
    co1Rec.stabilizerOrbits = [RecData.o0, RecData.o1, RecData.o2, RecData.o3] := rfl

theorem co1Rec_merges : co1Rec.merges =
    [⟨1, RecData.m0.map RecData.triple⟩, ⟨3, RecData.m1.map RecData.triple⟩,
      ⟨61, RecData.m2.map RecData.triple⟩] := rfl

theorem certVecArr_eq : certVecArr = CFSG.Sporadic.Co1Block.certVecs := by
  rw [certVecArr, co1Rec_vectors, Array.toArray_toList]

theorem certActArr_eq {k : Nat} (hk : k < 2) :
    certActArr k = CFSG.Sporadic.Co1Block.certAct k := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [certActArr, co1Rec_generatorActions, List.getD_cons_zero, Array.toArray_toList]
  · rw [certActArr, co1Rec_generatorActions, List.getD_cons_succ, List.getD_cons_zero,
      Array.toArray_toList]

end CFSG.Sporadic.Co1Schreier
