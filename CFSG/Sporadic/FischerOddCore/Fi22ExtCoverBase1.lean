
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverBase

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylow
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckBase
public import CFSG.Sporadic.FischerOddCore.LabelSpec
import Mathlib.Tactic.Group
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterCheckInputs
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
public import CFSG.Monster.B.Fischer.Fi22GraphCheck

@[expose] public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native

theorem fi22ExtElt_mem
    (x : Fin 1024 × Fin 32 × Fin 4) (e : Bool) : fi22ExtElt x e ∈ fi22ExtS := by
  have h1 : fi22ExtQ * fi22TProd x * fi22ExtQ⁻¹ ∈ fi22ExtS :=
    fi22ExtT0_le_S ⟨_, fi22TProd_mem x, conj_apply_eq _ _⟩
  cases e
  · rw [fi22ExtElt_false]
    exact h1
  · rw [fi22ExtElt_true]
    exact fi22ExtS.mul_mem h1 fi22ExtV_mem_S

theorem fi22ExtEltIdx_mem (I : ℕ) : fi22ExtEltIdx I ∈ fi22ExtS := by
  rw [fi22ExtEltIdx]
  exact fi22ExtElt_mem _ _

@[expose] def fi22ExtE
    (I : ℕ) : fi22ExtS := ⟨fi22ExtEltIdx I, fi22ExtEltIdx_mem I⟩

theorem fi22ExtE_val
    (I : ℕ) : (fi22ExtE I : Equiv.Perm (Fin 3510)) = fi22ExtEltIdx I := rfl

theorem unidxS_fi22TLevels (I : ℕ) (hI : I < 262144) :
    unidxS fi22TLevels I = (((fi22ExtCoord I).1.val, (fi22ExtCoord I).2.1.val,
      (fi22ExtCoord I).2.2.val), I % 2 == 1) := by
  have h1 : fi22TLevels[1]!.pts.size = 32 := fi22TLev_size (i := 1) (by norm_num)
  have h2 : fi22TLevels[2]!.pts.size = 4 := fi22TLev_size (i := 2) (by norm_num)
  simp only [unidxS, h1, h2, fi22ExtCoord]
  congr 2
  omega

theorem rep_fi22ExtQArr :
    Rep 3510 fi22ExtQArr fi22ExtQ := rep_fi22ExtQ

theorem rep_fi22ExtVArr :
    Rep 3510 fi22ExtVArr fi22ExtV := rep_fi22ExtV

theorem fi22ExtEltIdx_apply
    (I : ℕ) (p : Fin 3510) :
    ((fi22ExtEltIdx I p : Fin 3510) : ℕ) = fi22ExtQArr[tr3 fi22TLevels (fi22ExtCoord I).1.val
      (fi22ExtCoord I).2.1.val (fi22ExtCoord I).2.2.val
      fi22ExtQiArr[if (I % 2 == 1) then fi22ExtVArr[(p : ℕ)]! else (p : ℕ)]!]! := by
  have hv : (if (I % 2 == 1) then fi22ExtVArr[(p : ℕ)]! else (p : ℕ)) =
      (((if (I % 2 == 1) then fi22ExtV else 1) p : Fin 3510) : ℕ) := by
    by_cases h : (I % 2 == 1) = true
    · rw [ite_eq_left h, ite_eq_left h]
      exact rep_fi22ExtVArr p
    · rw [ite_eq_right h, ite_eq_right h, Equiv.Perm.one_apply]
  rw [hv, rep_fi22ExtQi, ← fi22TProd_apply, rep_fi22ExtQArr, fi22ExtEltIdx, fi22ExtElt,
    perm_mul4_apply]

theorem rep_fi22ExtFullArr
    {I : ℕ} (hI : I < 262144) :
    Rep 3510 (fi22ExtFullArr I) (fi22ExtEltIdx I) := fun p => by
  rw [fi22ExtFullArr, getElem!_ofFn_nat _ p.2]
  simp only
  rw [unidxS_fi22TLevels I hI, fi22ExtEltIdx_apply I p]

theorem rep_fi22ExtResArr
    {I : ℕ} (hI : I < 262144) :
    Rep 256 (fi22ExtResArr I) (fi22ExtRes (fi22ExtE I)) := fun i => by
  rw [fi22ExtResArr, resIdx, unidxS_fi22TLevels I hI]
  simp only
  rw [getElem!_ofFn_nat _ i.2]
  simp only [resPt]
  rw [fi22ExtDArr_get, ← fi22ExtEltIdx_apply I (fi22ExtDeltaPt i)]
  have h2 := fi22ExtRes_mk_apply (fi22ExtEltIdx I) (fi22ExtEltIdx_mem I) i
  rw [← h2, ← fi22ExtDArr_get]
  exact fi22ExtSylow_check.2.2.2.2.2.2.2.2.2.1 _ (fi22ExtRes ⟨_, fi22ExtEltIdx_mem I⟩ i).2

theorem fi22ExtE_idx (x : Fin 1024 × Fin 32 × Fin 4) (e : Bool) :
    (fi22ExtE (fi22ExtIdx x e) : Equiv.Perm (Fin 3510)) = fi22ExtElt x e := by
  rw [fi22ExtE_val, fi22ExtEltIdx, fi22ExtCoord_idx, fi22ExtIdx_mod]

theorem fi22ExtE_surj
    (s : fi22ExtS) : ∃ I < 262144, fi22ExtE I = s := by
  have hs : (s : Equiv.Perm (Fin 3510)) ∈ fi22ExtSx := fi22ExtS_eq_Sx ▸ s.2
  rcases hs with hs | hs
  · obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨x, rfl⟩ := fi22TProd_surj ht
    refine ⟨_, fi22ExtIdx_lt x false, Subtype.ext ?_⟩
    rw [fi22ExtE_idx, fi22ExtElt_false, ← hts, conj_apply_eq]
  · have hs' : (s : Equiv.Perm (Fin 3510)) * fi22ExtV⁻¹ ∈ fi22ExtT0 := by
      have := fi22ExtT0.mul_mem hs (fi22ExtT0.inv_mem fi22ExtV_sq_mem)
      convert this using 1
      group
    obtain ⟨t, ht, hts⟩ := hs'
    obtain ⟨x, rfl⟩ := fi22TProd_surj ht
    refine ⟨_, fi22ExtIdx_lt x true, Subtype.ext ?_⟩
    rw [fi22ExtE_idx, fi22ExtElt_true]
    rw [conj_apply_eq] at hts
    rw [hts, inv_mul_cancel_right]

theorem fi22ExtElt_inj
    {x y : Fin 1024 × Fin 32 × Fin 4} {e f : Bool}
    (h : fi22ExtElt x e = fi22ExtElt y f) : x = y ∧ e = f := by
  have key : ∀ x y : Fin 1024 × Fin 32 × Fin 4,
      fi22ExtQ * fi22TProd x * fi22ExtQ⁻¹ = fi22ExtQ * fi22TProd y * fi22ExtQ⁻¹ → x = y := by
    intro x y hxy
    apply fi22TProd_injective
    have e1 : fi22TProd x = fi22ExtQ⁻¹ * (fi22ExtQ * fi22TProd x * fi22ExtQ⁻¹) * fi22ExtQ := by
      group
    have e2 : fi22TProd y = fi22ExtQ⁻¹ * (fi22ExtQ * fi22TProd y * fi22ExtQ⁻¹) * fi22ExtQ := by
      group
    rw [e1, e2, hxy]
  have hmem : ∀ x : Fin 1024 × Fin 32 × Fin 4, fi22ExtQ * fi22TProd x * fi22ExtQ⁻¹ ∈ fi22ExtT0 :=
    fun x => ⟨_, fi22TProd_mem x, conj_apply_eq _ _⟩
  cases e <;> cases f
  · rw [fi22ExtElt_false, fi22ExtElt_false] at h
    exact ⟨key _ _ h, rfl⟩
  · exfalso
    rw [fi22ExtElt_false, fi22ExtElt_true] at h
    apply fi22ExtV_not_mem_T0
    have e : fi22ExtV = (fi22ExtQ * fi22TProd y * fi22ExtQ⁻¹)⁻¹ *
        (fi22ExtQ * fi22TProd x * fi22ExtQ⁻¹) := by
      rw [h]; group
    rw [e]
    exact fi22ExtT0.mul_mem (fi22ExtT0.inv_mem (hmem y)) (hmem x)
  · exfalso
    rw [fi22ExtElt_true, fi22ExtElt_false] at h
    apply fi22ExtV_not_mem_T0
    have e : fi22ExtV = (fi22ExtQ * fi22TProd x * fi22ExtQ⁻¹)⁻¹ *
        (fi22ExtQ * fi22TProd y * fi22ExtQ⁻¹) := by
      rw [← h]; group
    rw [e]
    exact fi22ExtT0.mul_mem (fi22ExtT0.inv_mem (hmem x)) (hmem y)
  · rw [fi22ExtElt_true, fi22ExtElt_true] at h
    exact ⟨key _ _ (mul_right_cancel h), rfl⟩

theorem fi22ExtE_inj
    {I J : ℕ} (hI : I < 262144) (hJ : J < 262144) (h : fi22ExtE I = fi22ExtE J) :
    I = J := by
  have h' : fi22ExtEltIdx I = fi22ExtEltIdx J := congrArg Subtype.val h
  rw [fi22ExtEltIdx, fi22ExtEltIdx] at h'
  obtain ⟨hc, he⟩ := fi22ExtElt_inj h'
  rw [← fi22ExtIdx_coord hI, ← fi22ExtIdx_coord hJ, hc, he]

@[expose] def fi22ExtGen
    (k : ℕ) : fi22ExtS :=
  if hk : k < 10 then ⟨fi22ExtFullGen k, fi22ExtFullGen_mem hk⟩ else 1

theorem rep_fi22ExtSteps
    {k : ℕ} (hk : k < fi22ExtSteps.size) :
    Rep 256 fi22ExtSteps[k]! (fi22ExtRes (fi22ExtGen k)) ∧
      Rep 256 fi22ExtStepsInv[k]! (fi22ExtRes (fi22ExtGen k))⁻¹ := by
  have hk' : k < 10 := by simpa [fi22ExtSteps] using hk
  have h1 : fi22ExtRes (fi22ExtGen k) = fi22ExtPerm256 k := by
    rw [fi22ExtGen, dite_eq_left hk']
    exact fi22ExtRes_fullGen hk'
  rw [h1, fi22ExtSteps_get hk', fi22ExtStepsInv_get hk']
  exact rep_permOfArr (fi22Ext_check.2.2.2.1 k (by omega))

theorem closure_fi22ExtGen :
    Subgroup.closure {x | ∃ s < fi22ExtSteps.size, fi22ExtGen s = x} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  have hg' := hg
  rw [fi22ExtS_eq_closure_full] at hg'
  revert hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    intro hx'
    obtain ⟨k, hk, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨k, by simpa [fi22ExtSteps] using hk, ?_⟩
    rw [fi22ExtGen, dite_eq_left hk]
  | one => intro _; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    intro hxy
    have hx' : x ∈ fi22ExtS := by rw [fi22ExtS_eq_closure_full]; exact hx
    have hy' : y ∈ fi22ExtS := by rw [fi22ExtS_eq_closure_full]; exact hy
    exact Subgroup.mul_mem _ (ihx hx') (ihy hy')
  | inv x hx ih =>
    intro hxi
    have hx' : x ∈ fi22ExtS := by rw [fi22ExtS_eq_closure_full]; exact hx
    exact Subgroup.inv_mem _ (ih hx')

theorem rep_fi22ExtRep_outer {k : ℕ} (hk : k < 3) :
    Rep 3510 (fi22ExtArr (24 + k)) (fi22ExtRep (3 + k)) := by
  have e : fi22ExtRep (3 + k) = fi22ExtPerm (24 + k) := by
    rw [fi22ExtRep]
    congr 1
    omega
  rw [e]
  exact rep_fi22ExtPerm (by omega)

end CFSG.Sporadic.FischerOddCore
