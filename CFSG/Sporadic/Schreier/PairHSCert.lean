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
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import Certificates.Certificate2218

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairText

@[expose] def hsSchemaVersion : ℕ := 1

@[expose] def hsGroupName : String := "HS"

@[expose] def hsPrime : ℕ := 2

@[expose] def hsDimension : ℕ := 20

@[expose] def hsBasisIdx : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18, 20, 24, 29, 33, 52]

@[expose] def hsVec (i : ℕ) : Fin 20 → ZMod 2 := CFSG.Sporadic.J1.toV 2 20 hsVectors[i]!

@[expose] def hsX : Set (Fin 20 → ZMod 2) := {v | ∃ i < 3850, hsVec i = v}

@[expose] def hsWords : Array (List ℤ) :=
  #[[], [],
    [-2, 1, -2, 1, 2, 1, 2],
    [-2, 1, -2, -2, -2, -2, 1, 2, 2, 2, 2, 1, 2],
    [4, 3, 4],
    [1, -2, -2, 1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 2, 1],
    [3, 6, 3],
    [1, -2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 1, 2, 2]]

@[expose] def hsBaseFin : List (Fin 3850) := [0, 1, 2, 3]

@[expose] def hsStrongPerm (j : ℕ) : Equiv.Perm (Fin 3850) := permOfArr 3850 hsStrongArrs[j]!

@[expose] def hsGen (k : ℕ) : Equiv.Perm (Fin 3850) := hsStrongPerm k

@[expose] def hsChain : RawSchreierDatum 3850 :=
  RawSchreierDatum.ofArrays 3850 (by decide) hsStrongArrs 2 (by simp [hsStrongArrs]) hsBaseFin
    (by decide) hsWords

@[expose] def hsP : Subgroup (Equiv.Perm (Fin 3850)) := Subgroup.closure {hsGen 0, hsGen 1}

@[expose] def hsPoint : ℕ := 0

@[expose] def hsStabIdx : List ℕ := [2, 3, 4, 5, 6, 7]

@[expose] def hsH0 : Subgroup (Equiv.Perm (Fin 3850)) :=
  Subgroup.closure {g | ∃ j ∈ hsStabIdx, hsStrongPerm j = g}

irreducible_def hsStabOrbits : List (List ℕ) := hsStabData.1

irreducible_def hsMerges : List (ℕ × List (ℕ × ℕ × ℕ)) := hsStabData.2

theorem hsCertOK_eq : hsCertOK = true :=
  Certificates.certificate2218

theorem hsCertOK_parts :
    hsVectors.size = 3850 ∧ (∀ i < 3850, CFSG.Sporadic.J1.Native.wfV 2 20 hsVectors[i]! = true) ∧
    (∀ j < 8, hsStrongArrs[j]!.size = 3850 ∧
      isInvA 3850 hsStrongArrs[j]! (rawInvs 3850 hsStrongArrs)[j]! = true) ∧
    hsStabOrbits.length = 12 ∧
    (∀ o ∈ hsStabOrbits, PairNative.strictInc o = true ∧ ∀ x ∈ o, x < 3850) ∧
    hsStabOrbits.map List.length = [1, 960, 160, 90, 192, 1440, 240, 360, 120, 240, 15, 32] ∧
    hsMerges.map Prod.fst = [1, 3, 4, 6, 7, 8, 36, 41, 93, 128, 158] ∧
    hsMerges.map (fun m => m.2.length) =
      [3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848] ∧
    ∀ m ∈ hsMerges, ∀ t ∈ m.2, t.1 < 2 ∧ t.2.1 < 3850 ∧ t.2.2 < 3850 := by
  have h := hsCertOK_eq
  simp only [hsCertOK, hsCertOKWith, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  rw [hsStabOrbits_def, hsMerges_def]
  refine ⟨h1, fun i hi => allLt_spec h2 hi, fun j hj => ?_, h4,
    fun o ho => ⟨(h5 o ho).1, fun x hx => (h5 o ho).2 x hx⟩, h6, h7, h8,
    fun m hm t ht => (h9 m hm t ht).1.elim fun a b => ⟨a, b, (h9 m hm t ht).2⟩⟩
  have := allLt_spec h3 hj
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem rep_hsStrongPerm {j : ℕ} (hj : j < 8) : Rep 3850 hsStrongArrs[j]! (hsStrongPerm j) :=
  (rep_permOfArr (hsCertOK_parts.2.2.1 j hj).2).1

theorem hsChain_strong_get (j : Fin hsChain.strongCount) :
    hsChain.strong.get j = hsStrongPerm j :=
  RawSchreierDatum.ofArrays_strong_get j

theorem hsChain_original_get (k : Fin hsChain.originalCount) :
    hsChain.original.get k = hsGen k :=
  RawSchreierDatum.ofArrays_original_get k

theorem hsChain_base : hsChain.base.toList.map Fin.val = [0, 1, 2, 3] := by
  rw [hsChain, RawSchreierDatum.ofArrays_base_toList]
  rfl

theorem hsP_eq_original : hsP = hsChain.originalSubgroup := by
  have e : hsChain.original.toList = [hsGen 0, hsGen 1] := by
    apply List.ext_getElem (by simp [hsChain, RawSchreierDatum.ofArrays])
    intro k h1 _
    have hk : k < hsChain.originalCount := by simpa using h1
    rw [Vector.getElem_toList]
    have := hsChain_original_get ⟨k, hk⟩
    rw [Vector.get] at this
    simp only [Fin.cast_mk] at this
    rw [show hsChain.original[k] = hsChain.original.toArray[k]'(by simpa using hk) from rfl, this]
    have hk2 : k < 2 := hk
    interval_cases k <;> rfl
  rw [hsP, RawSchreierDatum.originalSubgroup, e]
  congr 1
  ext g
  simp

theorem CERT_HS_matrix_action_data :
    hsSchemaVersion = 1 ∧ hsGroupName = "HS" ∧ hsPrime = 2 ∧ hsDimension = 20 ∧
    hsVectors.size = 3850 ∧
    (∀ i < 3850, hsVectors[i]!.length = 20 ∧ ∀ x ∈ hsVectors[i]!, x < 2) ∧
    hsBasisIdx = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18, 20, 24, 29, 33, 52] ∧
    hsChain.originalCount = 2 ∧ hsChain.strongCount = 8 ∧
    hsChain.base.toList.map Fin.val = [0, 1, 2, 3] ∧
    (∀ j < 8, Rep 3850 hsStrongArrs[j]! (hsStrongPerm j)) ∧
    (∀ j : Fin hsChain.strongCount, hsChain.strong.get j = hsStrongPerm j) ∧
    (∀ k : Fin hsChain.originalCount, hsChain.original.get k = hsGen k) ∧
    hsP = hsChain.originalSubgroup ∧
    hsPoint = 0 ∧ hsStabIdx = [2, 3, 4, 5, 6, 7] ∧
    hsStabOrbits.length = 12 ∧
    (∀ o ∈ hsStabOrbits, o.Pairwise (· < ·) ∧ ∀ x ∈ o, x < 3850) ∧
    hsStabOrbits.map List.length = [1, 960, 160, 90, 192, 1440, 240, 360, 120, 240, 15, 32] ∧
    hsMerges.map Prod.fst = [1, 3, 4, 6, 7, 8, 36, 41, 93, 128, 158] ∧
    hsMerges.map (fun m => m.2.length) =
      [3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848, 3848] ∧
    ∀ m ∈ hsMerges, ∀ t ∈ m.2, t.1 < 2 ∧ t.2.1 < 3850 ∧ t.2.2 < 3850 := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9⟩ := hsCertOK_parts
  refine ⟨rfl, rfl, rfl, rfl, h1, fun i hi => CFSG.Sporadic.J1.wfV_iff.1 (h2 i hi), rfl, rfl,
    by simp [hsChain, hsStrongArrs, RawSchreierDatum.ofArrays], hsChain_base,
    fun j hj => rep_hsStrongPerm hj, hsChain_strong_get, hsChain_original_get,
    hsP_eq_original, rfl, rfl,
    h4, fun o ho => ⟨pairwise_of_strictInc (h5 o ho).1, (h5 o ho).2⟩, h6, h7, h8, h9⟩

end CFSG.Sporadic.Schreier
