
module

public import CFSG.Sporadic.Schreier.Co1StabCheckBase
public import CFSG.Sporadic.Schreier.Co1FullOrbitsBase
public import CFSG.Sporadic.Schreier.Co1Propagate
public import CFSG.Sporadic.Schreier.Co1SplitMono
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import CFSG.Sporadic.Schreier.Co1OrbEnum
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.Co1XSet
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Schreier.Co1TernaryM12Cover

@[expose] public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply toVecD_xor toVecD_injective rowsMatrix)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix

noncomputable def stabH0 : GL24 := wordG [A₁, A₂] (Data.stabWord0.map Int.ofNat)

noncomputable def stabH1 : GL24 := wordG [A₁, A₂] (Data.stabWord1.map Int.ofNat)

noncomputable def stabH : Subgroup GL24 := Subgroup.closure {stabH0, stabH1}

noncomputable def stabVecOf (k : ℕ) : Vec24 := toVecD 24 (Native.stabVec k)

def fixSpace (v : Vec24) : Set Vec24 :=
  {u | ∀ h ∈ stabH, ((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v →
    ((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ u = u}

theorem stabH0_rep :
    MRep Native.hRows0 stabH0 := MRep.word ab_listRep _

theorem stabH1_rep :
    MRep Native.hRows1 stabH1 := MRep.word ab_listRep _

theorem stabH0_mem : stabH0 ∈ stabH := Subgroup.subset_closure (Set.mem_insert _ _)

theorem stabH1_mem : stabH1 ∈ stabH := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem stabH_le_GA : stabH ≤ GA := by
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  have hAB : ∀ x ∈ [A₁, A₂], x ∈ GA := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact A₁_mem
    · rw [hx]
      exact A₂_mem
  rcases hg with hg | hg
  · rw [hg]
    exact wordG_mem hAB _
  · rw [Set.mem_singleton_iff.mp hg]
    exact wordG_mem hAB _

noncomputable def witMats (m : ℕ) : List GL24 :=
  (Data.fixWords.getD m []).map fun w => wordG [stabH0, stabH1] w

theorem witMats_mem (m i : ℕ) : (witMats m).getD i 1 ∈ stabH := by
  refine getD_mem_of_forall (fun g hg => ?_) i
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  refine wordG_mem (fun x hx => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx
  · rw [hx]
    exact stabH0_mem
  · rw [hx]
    exact stabH1_mem

def fixN (m c : ℕ) (v : Fin 24) : ZMod 2 :=
  if Native.fixCoef (Native.witRows m) c v.val then 1 else 0

theorem exists_ab (z₁ z₂ v₁ v₂ u₁ u₂ : ZMod 2) (h : z₁ * v₂ ≠ z₂ * v₁) :
    ∃ a b : ZMod 2, u₁ = a * z₁ + b * v₁ ∧ u₂ = a * z₂ + b * v₂ := by
  revert z₁ z₂ v₁ v₂ u₁ u₂
  decide

theorem toVecD_testBit (n : ℕ) (j : Fin 24) :
    toVecD 24 n j = if n.testBit j.val then 1 else 0 := toVecD_apply 24 n j

def fixPts (v : Vec24) : Set Vec24 := kOrbit stabH v ∩ fixSpace v

theorem mem_enumSet_iff {cP cQ : Array ℕ} {root n : ℕ} {O : VOrbit}
    (h : Native.enumOK cP cQ root n O = true) {w : ℕ} (hw : w < 2 ^ 24) :
    toVecD 24 w ∈ enumSet O n ↔ Native.inEnum O n w = true := by
  obtain ⟨-, hall, -, -⟩ := enumOK_parts h
  simp only [Native.inEnum, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, (toVecD_injective hw (hall i hi).1 he).symm⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, by rw [he]⟩

theorem stabVec_lt (k : ℕ) (hk : k < 4) : Native.stabVec k < 2 ^ 24 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem mem_span_pair_iff {z v u : Vec24} :
    u ∈ Submodule.span (ZMod 2) {z, v} ↔ u = 0 ∨ u = z ∨ u = v ∨ u = z + v := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by rw [zero_smul, zero_smul, add_zero]⟩
    · exact ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
    · exact ⟨0, 1, by rw [zero_smul, one_smul, zero_add]⟩
    · exact ⟨1, 1, by rw [one_smul, one_smul]⟩

end CFSG.Sporadic.Co1Schreier
