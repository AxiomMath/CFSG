
module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.Schreier.PairF2Quad
public import CFSG.Sporadic.Schreier.PairText
public import CFSG.Sporadic.Schreier.PairClasses
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.Sporadic.Schreier.PairF2Quad
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.PairJ3CertInputs

@[expose] public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairText CFSG.Sporadic.Schreier.PairF2

def j3SchemaVersion : ℕ := 1

def j3GroupName : String := "J3"

def j3Prime : ℕ := 2

def j3Dimension : ℕ := 80

abbrev J3V : Type := Fin 80 → ZMod 2

def j3Quad (z : ℕ) : J3V → ZMod 2 := quadZ 80 z

def j3FormsBytes : ByteArray := j3FormsHex.toUTF8

def j3FormWord (r : ℕ) : ℕ := hexAt j3FormsBytes (810 * r) 810

def j3Form (r : ℕ) : J3V → ZMod 2 := j3Quad (j3FormWord r)

def j3X : Set (J3V → ZMod 2) := {q | ∃ r < 6156, j3Form r = q}

def j3InvForm : J3V → ZMod 2 := j3Quad j3InvWord

def j3B : Matrix (Fin 80) (Fin 80) (ZMod 2) := polarMatrix j3InvForm

def j3CentralizerIdx : List ℕ := [0, 1, 2, 3]

def j3CentralizerRank : ℕ := 6399

def j3Words : Array (List ℤ) :=
  #[[], [], [-2, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2],
    [-3, -3, 1, -3, -3, -3, 1, 3, 3, 3, 1, 3, 3],
    [-3, -3, 1, -3, 1, -3, -3, 1, 3, 3, 3, 3, 1, 3, 3, 3]]

def j3BaseFin : List (Fin 6156) := [0, 1, 3, 2]

def j3StrongPerm (j : ℕ) : Equiv.Perm (Fin 6156) := permOfArr 6156 j3StrongArrs[j]!

def j3Gen (k : ℕ) : Equiv.Perm (Fin 6156) := j3StrongPerm k

def j3Chain : RawSchreierDatum 6156 :=
  RawSchreierDatum.ofArrays 6156 (by decide) j3StrongArrs 2 (by simp [j3StrongArrs]) j3BaseFin
    (by decide) j3Words

def j3P : Subgroup (Equiv.Perm (Fin 6156)) := Subgroup.closure {j3Gen 0, j3Gen 1}

def j3Point : ℕ := 0

def j3StabIdx : List ℕ := [0, 2, 3, 4]

def j3H0 : Subgroup (Equiv.Perm (Fin 6156)) :=
  Subgroup.closure {g | ∃ j ∈ j3StabIdx, j3StrongPerm j = g}

theorem j3Chain_strong_get (j : Fin j3Chain.strongCount) :
    j3Chain.strong.get j = j3StrongPerm j :=
  RawSchreierDatum.ofArrays_strong_get j

theorem j3Chain_original_get (k : Fin j3Chain.originalCount) :
    j3Chain.original.get k = j3Gen k :=
  RawSchreierDatum.ofArrays_original_get k

theorem j3Chain_base : j3Chain.base.toList.map Fin.val = [0, 1, 3, 2] := by
  rw [j3Chain, RawSchreierDatum.ofArrays_base_toList]
  rfl

theorem j3P_eq_original : j3P = j3Chain.originalSubgroup := by
  have e : j3Chain.original.toList = [j3Gen 0, j3Gen 1] := by
    apply List.ext_getElem (by simp [j3Chain, RawSchreierDatum.ofArrays])
    intro k h1 _
    have hk : k < j3Chain.originalCount := by simpa using h1
    rw [Vector.getElem_toList]
    have := j3Chain_original_get ⟨k, hk⟩
    rw [Vector.get] at this
    simp only [Fin.cast_mk] at this
    rw [show j3Chain.original[k] = j3Chain.original.toArray[k]'(by simpa using hk) from rfl, this]
    have hk2 : k < 2 := hk
    interval_cases k <;> rfl
  rw [j3P, RawSchreierDatum.originalSubgroup, e]
  congr 1
  ext g
  simp

end CFSG.Sporadic.Schreier
