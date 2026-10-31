
module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.J1.VecSpec
public import CFSG.Sporadic.Schreier.PairText
public import CFSG.Sporadic.Schreier.PairClasses
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.J1.Vec
public import CFSG.Sporadic.Schreier.PairMcLCertInputs

@[expose] public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairText

def mclSchemaVersion : ℕ := 1

def mclGroupName : String := "McL"

def mclPrime : ℕ := 3

def mclDimension : ℕ := 21

def mclBasisIdx : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21]

def mclVec (i : ℕ) : Fin 21 → ZMod 3 := CFSG.Sporadic.J1.toV 3 21 mclVectors[i]!

def mclX : Set (Fin 21 → ZMod 3) := {v | ∃ i < 275, mclVec i = v}

def mclWords : Array (List ℤ) :=
  #[[], [],
    [-2, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2],
    [-2, -2, 1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 2],
    [4, 3, 1, 4, 3],
    [1, 3, 1, 4, 1, 3, 1],
    [6, -5, 6, 5, 5, 6, 5, 5, 5],
    [-2, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2],
    [3, -8, 4, 8],
    [-9, -5, 6, 9],
    [-10, 7, -10, 7, 10, 7, 10],
    [-5, 9, 6, 5],
    [7, -12, 10, 12]]

def mclBaseFin : List (Fin 275) := [0, 1, 2, 3, 4]

def mclStrongPerm (j : ℕ) : Equiv.Perm (Fin 275) := permOfArr 275 mclStrongArrs[j]!

def mclGen (k : ℕ) : Equiv.Perm (Fin 275) := mclStrongPerm k

def mclChain : RawSchreierDatum 275 :=
  RawSchreierDatum.ofArrays 275 (by decide) mclStrongArrs 2 (by simp [mclStrongArrs]) mclBaseFin
    (by decide) mclWords

def mclP : Subgroup (Equiv.Perm (Fin 275)) := Subgroup.closure {mclGen 0, mclGen 1}

def mclPoint : ℕ := 0

def mclStabIdx : List ℕ := [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def mclH0 : Subgroup (Equiv.Perm (Fin 275)) :=
  Subgroup.closure {g | ∃ j ∈ mclStabIdx, mclStrongPerm j = g}

irreducible_def mclStabOrbits : List (List ℕ) := mclStabData.1

irreducible_def mclMerges : List (ℕ × List (ℕ × ℕ × ℕ)) := mclStabData.2

theorem mclChain_strong_get (j : Fin mclChain.strongCount) :
    mclChain.strong.get j = mclStrongPerm j :=
  RawSchreierDatum.ofArrays_strong_get j

theorem mclChain_original_get (k : Fin mclChain.originalCount) :
    mclChain.original.get k = mclGen k :=
  RawSchreierDatum.ofArrays_original_get k

theorem mclChain_base : mclChain.base.toList.map Fin.val = [0, 1, 2, 3, 4] := by
  rw [mclChain, RawSchreierDatum.ofArrays_base_toList]
  rfl

theorem mclP_eq_original : mclP = mclChain.originalSubgroup := by
  have e : mclChain.original.toList = [mclGen 0, mclGen 1] := by
    apply List.ext_getElem (by simp [mclChain, RawSchreierDatum.ofArrays])
    intro k h1 _
    have hk : k < mclChain.originalCount := by simpa using h1
    rw [Vector.getElem_toList]
    have := mclChain_original_get ⟨k, hk⟩
    rw [Vector.get] at this
    simp only [Fin.cast_mk] at this
    rw [show mclChain.original[k] = mclChain.original.toArray[k]'(by simpa using hk) from rfl, this]
    have hk2 : k < 2 := hk
    interval_cases k <;> rfl
  rw [mclP, RawSchreierDatum.originalSubgroup, e]
  congr 1
  ext g
  simp

end CFSG.Sporadic.Schreier
