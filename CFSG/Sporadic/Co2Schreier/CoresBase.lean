
module

public import CFSG.Sporadic.Co2Schreier.Action
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public meta import Std.Data.HashMap
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Schreier.CoreCheckBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

theorem coreOK_spec {gens conj pis : Array (Array ℕ)} {m : ℕ} {cen : List ℕ} {E : LeftEnum}
    (h : coreOK gens conj pis m cen E = true) :
    enumOK gens m E = true ∧ conjOK conj pis m E = true ∧ centerIdx gens m E = cen := by
  simp only [coreOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem normal_of_conj_mem {H K : Subgroup (Equiv.Perm (Fin 2300))}
    (h : ∀ c ∈ K, ∀ x ∈ H, c * x * c⁻¹ ∈ H) : (H.subgroupOf K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact h g g.2 n hn

theorem chainQAction_arrays :
    ChainArrays chainQAction localRec.chains.qAction.origArrs
    localRec.chains.qAction.strongArrs localRec.chains.qAction.baseArr
    localRec.chains.qAction.wordArrs := chainQAction_records.2.2

theorem chainRAction_arrays :
    ChainArrays chainRAction localRec.chains.rAction.origArrs
    localRec.chains.rAction.strongArrs localRec.chains.rAction.baseArr
    localRec.chains.rAction.wordArrs := chainRAction_records.2.2

theorem chainQAction_original :
    chainQAction.originalSubgroup =
      Subgroup.closure {π | ∃ i < cTuple.length, permOfArr 512
        localRec.chains.qAction.origArrs[i]! = π} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext π
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  unfold chainQAction
  rw [original_toList_rawOfArrays, localShape.chainQ.origArrs_size, cTuple_length]

theorem chainRAction_original :
    chainRAction.originalSubgroup =
      Subgroup.closure {π | ∃ i < dTuple.length, permOfArr 2048
        localRec.chains.rAction.origArrs[i]! = π} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext π
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  unfold chainRAction
  rw [original_toList_rawOfArrays, localShape.chainR.origArrs_size, dTuple_length]

theorem card_center_eq {H : Subgroup (Equiv.Perm (Fin 2300))} :
    Nat.card (Subgroup.center H) = Nat.card (CFSG.centerIn H) := by
  rw [CFSG.centerIn_eq_map_center, Subgroup.card_map_of_injective H.subtype_injective]

theorem centerIn_le_inf {H K : Subgroup (Equiv.Perm (Fin 2300))} (hHK : H ≤ K) :
    CFSG.centerIn H ≤ K ⊓ Subgroup.centralizer (H : Set (Equiv.Perm (Fin 2300))) := fun _ hx =>
  ⟨hHK (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩

end CFSG.Sporadic.Co2Schreier
