module

public import CFSG.Sporadic.Schreier.ONLocalOrders
public import CFSG.Sporadic.Schreier.ONCheckAux

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates
open scoped commutatorElement

theorem prep_onLgens :
    ∀ j (hj : j < onLgens.length), PRep N (wordArrs Data.LWords)[j]! onLgens[j] :=
  prep_wordArrs words_ok.2.2.1

theorem onL_le_M :
    onL ≤ onM := by
  rw [onL, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hj2 : j < 2 := by rw [onLgens_length] at hj; exact hj
  have h := mFacts.mem (prep_onLgens j hj) (evalList_mem (List.getElem_mem hj))
    (allBelowN_spec qt_cert.2.2.2.2.2.2.2 hj2)
  rwa [onMChain_sub] at h

theorem card_L_subgroupOf :
    Nat.card (onL.subgroupOf onM) = 80640 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onL_le_M).toEquiv, card_onL]

theorem onL_relIndex :
    onL.relIndex onM = 2 := by
  have h := (onL.subgroupOf onM).card_mul_index
  rw [card_L_subgroupOf, card_onM] at h
  rw [Subgroup.relIndex]
  omega

theorem commutator_M_le_L :
    ⁅onM, onM⁆ ≤ onL := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h2 : (onL.subgroupOf onM).index = 2 := onL_relIndex
  have key : (⁅(⟨a, ha⟩ : onM), ⟨b, hb⟩⁆ : onM) ∈ onL.subgroupOf onM := by
    rw [commutatorElement_def, mul_assoc, Subgroup.mul_mem_iff_of_index_two h2,
      Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mul_mem_iff_of_index_two h2,
      inv_mem_iff, inv_mem_iff]
  rw [Subgroup.mem_subgroupOf] at key
  exact key

theorem listComm_eq {G : Type*} [Group G] (g : List G) (a b : ℕ) :
    listComm g a b = ⁅g.getD (b - 1) 1, g.getD (a - 1) 1⁆ := by
  rw [listComm, commutatorElement_def]

theorem getD_mem {G : Type*} [Group G] {H : Subgroup G} {g : List G} (hg : ∀ x ∈ g, x ∈ H)
    (i : ℕ) : g.getD i 1 ∈ H := by
  by_cases hi : i < g.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hg _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact one_mem H

theorem commSpec_mem_commutator {G : Type*} [Group G] {H : Subgroup G} {g : List G}
    (hg : ∀ x ∈ g, x ∈ H) (s : ℕ × ℕ × ℕ) : commSpec g s ∈ ⁅H, H⁆ := by
  have hc : ∀ x ∈ H, ∀ y ∈ H, ∀ k ∈ H, k * ⁅x, y⁆ * k⁻¹ ∈ ⁅H, H⁆ := by
    intro x hx y hy k hk
    have e : k * ⁅x, y⁆ * k⁻¹ = ⁅k * x * k⁻¹, k * y * k⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (mul_mem (mul_mem hk hx) (inv_mem hk))
      (mul_mem (mul_mem hk hy) (inv_mem hk))
  unfold commSpec
  split_ifs
  · rw [listComm_eq]
    exact Subgroup.commutator_mem_commutator (getD_mem hg _) (getD_mem hg _)
  · rw [listComm_eq]
    exact hc _ (getD_mem hg _) _ (getD_mem hg _) _ (getD_mem hg _)

theorem onWM_le :
    onWM ≤ ⁅onM, onM⁆ := by
  rw [onWM, Subgroup.closure_le]
  intro g hg
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hg
  exact commSpec_mem_commutator (fun x hx => Subgroup.subset_closure hx) s

theorem onWL_le :
    onWL ≤ ⁅onL, onL⁆ := by
  rw [onWL, Subgroup.closure_le]
  intro g hg
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hg
  exact commSpec_mem_commutator (fun x hx => Subgroup.subset_closure hx) s

theorem onL_eq_commutator :
    onL = ⁅onM, onM⁆ := by
  have h1 : onWM = onL :=
    Subgroup.eq_of_le_of_card_ge (onWM_le.trans commutator_M_le_L) (by rw [card_onL, card_onWM])
  exact le_antisymm (h1.symm.le.trans onWM_le) commutator_M_le_L

theorem onL_commutator :
    ⁅onL, onL⁆ = onL := by
  have hle : ⁅onL, onL⁆ ≤ onL := Subgroup.commutator_le_self onL
  have h1 : onWL = onL :=
    Subgroup.eq_of_le_of_card_ge (onWL_le.trans hle) (by rw [card_onL, card_onWL])
  exact le_antisymm hle (h1.symm.le.trans onWL_le)

instance onL_isPerfect :
    Group.IsPerfect onL := Subgroup.isPerfect_iff.2 onL_commutator

theorem commutator_M_eq :
    commutator onM = onL.subgroupOf onM := by
  apply Subgroup.map_injective onM.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 onL_le_M, commutator_def,
    Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    onL_eq_commutator]

instance onL_characteristic :
    (onL.subgroupOf onM).Characteristic := by
  rw [← commutator_M_eq]
  infer_instance

theorem at_on_perfect_derived_subgroup :
    onL = ⁅onM, onM⁆ ∧ Nat.card onL = 80640 ∧ onL.relIndex onM = 2 ∧ ⁅onL, onL⁆ = onL ∧
      Group.IsPerfect onL ∧ (onL.subgroupOf onM).Characteristic :=
  ⟨onL_eq_commutator, card_onL, onL_relIndex, onL_commutator, onL_isPerfect,
    onL_characteristic⟩

end CFSG.ONSchreier
