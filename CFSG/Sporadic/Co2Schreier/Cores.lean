
module

public import CFSG.Sporadic.Co2Schreier.CoresBase

public import CFSG.Sporadic.Co2Schreier.Action
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Schreier.Chains
public import CFSG.Sporadic.Co2Schreier.CoreCheck

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

theorem enumQ_facts : EnumFacts qArrs 512 enumQ :=
  enumFacts_of (by norm_num) (coreOK_spec coreQ_check.1).1

theorem enumR_facts : EnumFacts rArrs 2048 enumR :=
  enumFacts_of (by norm_num) (coreOK_spec coreR_check.1).1

theorem card_locQ :
    Nat.card locQ = 512 := enumQ_facts.card repTuple_q

theorem card_locR :
    Nat.card locR = 2048 := enumR_facts.card repTuple_r

instance locQ_normal :
    (locQ.subgroupOf locC).Normal :=
  normal_of_conj_mem fun _ hc _ hx => enumQ_facts.conj_mem repTuple_q repTuple_c wordFacts.invC
    (coreOK_spec coreQ_check.1).2.1 hc hx

instance locR_normal :
    (locR.subgroupOf locD).Normal :=
  normal_of_conj_mem fun _ hc _ hx => enumR_facts.conj_mem repTuple_r repTuple_d wordFacts.invD
    (coreOK_spec coreR_check.1).2.1 hc hx

theorem card_chainQAction :
    Nat.card chainQAction.originalSubgroup = 371589120 := by
  rw [card_originalSubgroup_of_chainOK chainQAction_arrays (by norm_num) chainQAction_check.1]
  change (recordOrbits 512 localRec.chains.qAction).prod = _
  rw [chainQAction_check.2]
  rfl

theorem card_chainRAction :
    Nat.card chainRAction.originalSubgroup = 1290240 := by
  rw [card_originalSubgroup_of_chainOK chainRAction_arrays (by norm_num) chainRAction_check.1]
  change (recordOrbits 2048 localRec.chains.rAction).prod = _
  rw [chainRAction_check.2]
  rfl

theorem card_conjNormal_Q :
    Nat.card (MulAut.conjNormal (H := locQ.subgroupOf locC)).range = 371589120 := by
  rw [← card_chainQAction, chainQAction_original]
  exact card_range_conjNormal enumQ_facts repTuple_q locQ_le_C (hN := locQ_normal) repTuple_c
    wordFacts.invC (coreOK_spec coreQ_check.1).2.1 fun i hi =>
      localShape.chainQ.orig_inv (by rwa [cTuple_length] at hi)

theorem card_conjNormal_R :
    Nat.card (MulAut.conjNormal (H := locR.subgroupOf locD)).range = 1290240 := by
  rw [← card_chainRAction, chainRAction_original]
  exact card_range_conjNormal enumR_facts repTuple_r locR_le_D (hN := locR_normal) repTuple_d
    wordFacts.invD (coreOK_spec coreR_check.1).2.1 fun i hi =>
      localShape.chainR.orig_inv (by rwa [dTuple_length] at hi)

theorem card_centerIn_Q :
    Nat.card (CFSG.centerIn locQ) = 2 := by
  have h := enumQ_facts.card_centerIn repTuple_q
  rw [(coreOK_spec coreQ_check.1).2.2] at h
  exact h

theorem card_centerIn_R :
    Nat.card (CFSG.centerIn locR) = 32 := by
  have h := enumR_facts.card_centerIn repTuple_r
  rw [(coreOK_spec coreR_check.1).2.2] at h
  exact h

theorem eltE_Q_z :
    eltE enumQ 23 = locZ :=
  eq_of_eqA (enumQ_facts.rep (by norm_num)) rep_z coreQ_check.2

theorem eltE_R_z :
    eltE enumR 617 = locZ :=
  eq_of_eqA (enumR_facts.rep (by norm_num)) rep_z coreR_check.2.1

theorem eltE_R_t :
    eltE enumR 434 = locT :=
  eq_of_eqA (enumR_facts.rep (by norm_num)) rep_t coreR_check.2.2

theorem locZ_mem_centerIn_Q :
    locZ ∈ CFSG.centerIn locQ := by
  rw [← eltE_Q_z]
  refine (enumQ_facts.mem_centerIn_iff repTuple_q (by norm_num)).2 ?_
  rw [(coreOK_spec coreQ_check.1).2.2]
  simp

theorem locZ_mem_centerIn_R :
    locZ ∈ CFSG.centerIn locR := by
  rw [← eltE_R_z]
  refine (enumR_facts.mem_centerIn_iff repTuple_r (by norm_num)).2 ?_
  rw [(coreOK_spec coreR_check.1).2.2]
  decide

theorem locT_mem_centerIn_R :
    locT ∈ CFSG.centerIn locR := by
  rw [← eltE_R_t]
  refine (enumR_facts.mem_centerIn_iff repTuple_r (by norm_num)).2 ?_
  rw [(coreOK_spec coreR_check.1).2.2]
  decide

theorem locC_inf_centralizer_Q :
    locC ⊓ Subgroup.centralizer (locQ : Set (Equiv.Perm (Fin 2300))) = CFSG.centerIn locQ := by
  have h := card_inf_centralizer_mul locQ_le_C (hN := locQ_normal)
  change Nat.card ↥(locC ⊓ Subgroup.centralizer (locQ : Set (Equiv.Perm (Fin 2300)))) *
    Nat.card (MulAut.conjNormal (H := locQ.subgroupOf locC)).range = Nat.card locC at h
  rw [card_conjNormal_Q, card_locC] at h
  have hcard : Nat.card ↥(locC ⊓ Subgroup.centralizer
      (locQ : Set (Equiv.Perm (Fin 2300)))) = 2 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 371589120) (h.trans (by norm_num))
  exact (Subgroup.eq_of_le_of_card_ge (centerIn_le_inf locQ_le_C)
    (by rw [hcard, card_centerIn_Q])).symm

theorem locD_inf_centralizer_R :
    locD ⊓ Subgroup.centralizer (locR : Set (Equiv.Perm (Fin 2300))) = CFSG.centerIn locR := by
  have h := card_inf_centralizer_mul locR_le_D (hN := locR_normal)
  change Nat.card ↥(locD ⊓ Subgroup.centralizer (locR : Set (Equiv.Perm (Fin 2300)))) *
    Nat.card (MulAut.conjNormal (H := locR.subgroupOf locD)).range = Nat.card locD at h
  rw [card_conjNormal_R, card_locD] at h
  have hcard : Nat.card ↥(locD ⊓ Subgroup.centralizer
      (locR : Set (Equiv.Perm (Fin 2300)))) = 32 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1290240) (h.trans (by norm_num))
  exact (Subgroup.eq_of_le_of_card_ge (centerIn_le_inf locR_le_D)
    (by rw [hcard, card_centerIn_R])).symm

theorem AT_Co2_normal_core_centralizers :
    locQ ≤ locC ∧ locR ≤ locD ∧ (locQ.subgroupOf locC).Normal ∧ (locR.subgroupOf locD).Normal ∧
    Nat.card locQ = 512 ∧ Nat.card locR = 2048 ∧
    Nat.card (Subgroup.center locQ) = 2 ∧ Nat.card (Subgroup.center locR) = 32 ∧
    locZ ∈ CFSG.centerIn locQ ⊓ CFSG.centerIn locR ∧ locT ∈ CFSG.centerIn locR ∧
    Nat.card (MulAut.conjNormal (H := locQ.subgroupOf locC)).range = 371589120 ∧
    Nat.card (MulAut.conjNormal (H := locR.subgroupOf locD)).range = 1290240 ∧
    locC ⊓ Subgroup.centralizer (locQ : Set (Equiv.Perm (Fin 2300))) = CFSG.centerIn locQ ∧
    locD ⊓ Subgroup.centralizer (locR : Set (Equiv.Perm (Fin 2300))) = CFSG.centerIn locR :=
  ⟨locQ_le_C, locR_le_D, locQ_normal, locR_normal, card_locQ, card_locR,
    card_center_eq.trans card_centerIn_Q, card_center_eq.trans card_centerIn_R,
    Subgroup.mem_inf.2 ⟨locZ_mem_centerIn_Q, locZ_mem_centerIn_R⟩, locT_mem_centerIn_R,
    card_conjNormal_Q, card_conjNormal_R, locC_inf_centralizer_Q, locD_inf_centralizer_R⟩

end CFSG.Sporadic.Co2Schreier
