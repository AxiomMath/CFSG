module

public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Quasithin.Recognition.CertTrialityModel
public import CFSG.Quasithin.Recognition.CertDataTriality
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Quasithin.Recognition.CertF8
public meta import CFSG.Quasithin.Recognition.CertTrialityModel
public meta import CFSG.Quasithin.Recognition.CertDataTriality
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

instance : Inhabited GF8 := ⟨0⟩

@[expose] def dataLines (s : String) : List String := (s.splitOn "\n").filter fun l => !l.isEmpty

@[expose] def pointArr : Array (Array GF8) :=
  ((dataLines trialityPointsText).map fun l =>
    (l.toList.map fun c => GF8.ofNat' (c.toNat - '0'.toNat)).toArray).toArray

@[expose] def pointVec (i : ℕ) : Fin 8 → GF8 := fun j => (pointArr[i]!)[(j : ℕ)]!

@[expose] def vecOfArr (a : Array GF8) : Fin 8 → GF8 := fun j => a[(j : ℕ)]!

@[expose] def packVec (v : Fin 8 → GF8) : ℕ :=
  (v 0).toNat + 8 * ((v 1).toNat + 8 * ((v 2).toNat + 8 * ((v 3).toNat + 8 * ((v 4).toNat +
    8 * ((v 5).toNat + 8 * ((v 6).toNat + 8 * (v 7).toNat))))))

@[expose] def packArr (a : Array GF8) : ℕ := packVec (vecOfArr a)

@[expose] def pointIndex : Std.HashMap ℕ ℕ :=
  (List.range 2457).foldl (fun m i => m.insert (packArr pointArr[i]!) i) {}

@[expose] def leadArr (a : Array GF8) : GF8 := (a.find? fun x => x ≠ 0).getD 0

@[expose] def normArr (a : Array GF8) : Array GF8 :=
  let c := (leadArr a)⁻¹
  a.map fun x => c * x

@[expose] def IsNormalized (v : Fin 8 → GF8) : Prop :=
  ∃ t : Fin 8, v t = 1 ∧ ∀ s : Fin 8, s < t → v s = 0

instance (v : Fin 8 → GF8) : Decidable (IsNormalized v) :=
  inferInstanceAs (Decidable (∃ t : Fin 8, v t = 1 ∧ ∀ s : Fin 8, s < t → v s = 0))

@[expose] def dotArr (r a : Array GF8) : GF8 :=
  r[0]! * a[0]! + r[1]! * a[1]! + r[2]! * a[2]! + r[3]! * a[3]! + r[4]! * a[4]! +
    r[5]! * a[5]! + r[6]! * a[6]! + r[7]! * a[7]!

@[expose] def mulVecArr (M : Array (Array GF8)) (a : Array GF8) : Array GF8 :=
  Array.ofFn (n := 8) fun i => dotArr M[(i : ℕ)]! a

@[expose] def rowsOfMat (M : Matrix (Fin 8) (Fin 8) GF8) : Array (Array GF8) :=
  Array.ofFn (n := 8) fun i => Array.ofFn (n := 8) fun j => M i j

@[expose] def actIdxArr (M : Array (Array GF8)) (i : ℕ) : ℕ :=
  pointIndex.getD (packArr (normArr (mulVecArr M pointArr[i]!))) 0

@[expose] def actOKArr (M : Array (Array GF8)) : Bool :=
  allLt 2457 fun i =>
    let w := normArr (mulVecArr M pointArr[i]!)
    let j := pointIndex.getD (packArr w) 0
    decide (j < 2457) && (pointArr[j]! == w)

@[expose] def trialityGenList : List (Matrix (Fin 8) (Fin 8) GF8) :=
  [true, false].flatMap (fun s => (List.finRange 8).map fun i => trialityElt ⟨i⟩ s) ++
    [trialityMid true, trialityMid false]

@[expose] def witnessDigits : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 1, 1, 1, 1, 0, 0], [0, 0, 1, 2, 4, 3, 0, 0],
    [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 1], [1, 0, 1, 1, 1, 1, 0, 0],
    [0, 1, 1, 2, 4, 3, 0, 0]]

@[expose] def witnessIdx : List ℕ := [0, 8, 80, 657, 2385, 2456, 187, 197, 1, 24, 81, 728, 1812, 17, 78]

@[expose] def vecOfDigits (l : List ℕ) : Fin 8 → GF8 := fun j => GF8.ofNat' (l.getD (j : ℕ) 0)

@[expose] def pointsOK : Bool :=
  allLt 2457 fun i => decide (pointVec i ≠ 0) && decide (IsNormalized (pointVec i)) &&
    (pointIndex.getD (packArr pointArr[i]!) 0 == i)

@[expose] def witnessOK : Bool :=
  allLt 15 fun t => decide (pointVec (witnessIdx.getD t 0) = vecOfDigits (witnessDigits.getD t []))

@[expose] def actArray (M : Array (Array GF8)) : Array ℕ := (Array.range 2457).map (actIdxArr M)

@[expose] def trialityGens : Array (Array ℕ) :=
  trialityGenList.toArray.map fun M => actArray (rowsOfMat M)

@[expose] def trialityWords : Array (List ℤ) :=
  CFSG.YGroups.ModelNative.chainWords trialityChainText

@[expose] def trialityBase : List (Fin 2457) := [1, 9, 2, 17, 83]

@[expose] def trialityStrong : Array (Array ℕ) :=
  (CFSG.YGroups.ModelNative.strongOf 2457 trialityGens trialityWords).1

@[expose] def trialityRawWords : Array (List ℤ) := Array.replicate 18 [] ++ trialityWords

end CFSG.Quasithin
