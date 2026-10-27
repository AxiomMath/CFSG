module

public import CFSG.Monster.B.Mathieu.CertText0
public import CFSG.Monster.B.Mathieu.CertText1
public import CFSG.Monster.B.Mathieu.CertText2
public import CFSG.Monster.B.Mathieu.CertText3
public import CFSG.Monster.B.Mathieu.CertText4
public import CFSG.Monster.B.Mathieu.CertText5
public import CFSG.Certificates.NativeValidSchreier

public section

namespace CFSG.Monster.B.Mathieu

open Lean (Json)
open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def certificateText : String :=
  certText0 ++ certText1 ++ certText2 ++ certText3 ++ certText4 ++ certText5

structure ChainRecord where
  degree : ℕ
  generators : List (List ℕ)
  base : List ℕ
  strongGenerators : List (List ℕ)
  derivations : List (List ℤ)
  deriving DecidableEq, Inhabited

structure NormalGenRecord where
  representative : List ℕ
  conjugators : List (List ℤ)
  chain : ChainRecord
  deriving DecidableEq, Inhabited

structure SylowRecord where
  prime : ℕ
  generators : List (List ℕ)
  normalGeneration : List NormalGenRecord
  deriving DecidableEq, Inhabited

structure GroupRecord where
  group : String
  seedPaths : List String
  chain : ChainRecord
  sylows : List SylowRecord
  deriving DecidableEq, Inhabited

structure CertificateFile where
  schemaVersion : ℕ
  description : String
  permutationConvention : String
  groups : List GroupRecord
  deriving DecidableEq, Inhabited

@[expose] def ChainRecord.ofJson (j : Json) : Except String ChainRecord := do
  pure
    { degree := ← j.getObjValAs? ℕ "degree"
      generators := ← j.getObjValAs? (List (List ℕ)) "generators"
      base := ← j.getObjValAs? (List ℕ) "base"
      strongGenerators := ← j.getObjValAs? (List (List ℕ)) "strong_generators"
      derivations := ← j.getObjValAs? (List (List ℤ)) "derivations" }

@[expose] def NormalGenRecord.ofJson (j : Json) : Except String NormalGenRecord := do
  pure
    { representative := ← j.getObjValAs? (List ℕ) "representative"
      conjugators := ← j.getObjValAs? (List (List ℤ)) "conjugators"
      chain := ← ChainRecord.ofJson (← j.getObjVal? "chain") }

@[expose] def SylowRecord.ofJson (j : Json) : Except String SylowRecord := do
  let ng ← (← (← j.getObjVal? "normal_generation").getArr?).toList.mapM NormalGenRecord.ofJson
  pure
    { prime := ← j.getObjValAs? ℕ "prime"
      generators := ← j.getObjValAs? (List (List ℕ)) "generators"
      normalGeneration := ng }

@[expose] def GroupRecord.ofJson (j : Json) : Except String GroupRecord := do
  let sy ← (← (← j.getObjVal? "sylows").getArr?).toList.mapM SylowRecord.ofJson
  pure
    { group := ← j.getObjValAs? String "group"
      seedPaths := ← j.getObjValAs? (List String) "seed_paths"
      chain := ← ChainRecord.ofJson (← j.getObjVal? "chain")
      sylows := sy }

@[expose] def CertificateFile.ofJson (j : Json) : Except String CertificateFile := do
  let gs ← (← (← j.getObjVal? "groups").getArr?).toList.mapM GroupRecord.ofJson
  pure
    { schemaVersion := ← j.getObjValAs? ℕ "schema_version"
      description := ← j.getObjValAs? String "description"
      permutationConvention := ← j.getObjValAs? String "permutation_convention"
      groups := gs }

@[expose] def certificateFile : Except String CertificateFile := do
  CertificateFile.ofJson (← Json.parse certificateText)

@[expose] def MathieuCertificate (t : String) : Option GroupRecord :=
  match certificateFile with
  | .ok f => f.groups.find? fun r => r.group == t
  | .error _ => none

@[expose] noncomputable def arrPerm (n : ℕ) (a : List ℕ) : Equiv.Perm (Fin n) :=
  permOfArr n a.toArray

@[expose] def letterValue {G : Type*} [Group G] (gs : List G) (l : ℤ) : G :=
  if 0 < l then gs.getD (l.natAbs - 1) 1 else (gs.getD (l.natAbs - 1) 1)⁻¹

@[expose] def wordValue {G : Type*} [Group G] (gs : List G) (w : List ℤ) : G :=
  (w.map (letterValue gs)).prod

@[expose] noncomputable def GroupRecord.rootGens (r : GroupRecord) (n : ℕ) :
    List (Equiv.Perm (Fin n)) :=
  r.chain.generators.map (arrPerm n)

@[expose] noncomputable def NormalGenRecord.conjugates {n : ℕ} (ng : NormalGenRecord)
    (gs : List (Equiv.Perm (Fin n))) : List (Equiv.Perm (Fin n)) :=
  ng.conjugators.map fun w => (wordValue gs w)⁻¹ * arrPerm n ng.representative * wordValue gs w

@[expose] def ChainRecord.origArrs (c : ChainRecord) : Array (Array ℕ) :=
  (c.generators.map List.toArray).toArray

@[expose] def ChainRecord.strongArrs (c : ChainRecord) : Array (Array ℕ) :=
  (c.strongGenerators.map List.toArray).toArray

@[expose] def ChainRecord.baseArr (c : ChainRecord) : Array ℕ := c.base.toArray

@[expose] def ChainRecord.wordArrs (c : ChainRecord) : Array (List ℤ) :=
  (List.replicate c.generators.length [] ++ c.derivations).toArray

@[expose] def ChainRecord.Records (c : ChainRecord) {n : ℕ} (Q : RawSchreierDatum n) : Prop :=
  c.degree = n ∧ c.generators.length + c.derivations.length = c.strongGenerators.length ∧
    ChainArrays Q c.origArrs c.strongArrs c.baseArr c.wordArrs

end CFSG.Monster.B.Mathieu
