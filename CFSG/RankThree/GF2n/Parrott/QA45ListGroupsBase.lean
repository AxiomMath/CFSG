
module

public import Certificates.Data.ParrottPSp43L1
public import CFSG.RankThree.GF2n.Parrott.SylowHFacts
public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree
public import CFSG.GroupTheory.ConjTransport
public import Certificates.Certificate946017Base

@[expose] public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups
open CFSG.Sporadic.Schreier (tab tab_eq)

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def QA45SubgroupConj (E F : Subgroup ↥QA45.originalSubgroup) : Prop :=
  ∃ g : ↥QA45.originalSubgroup, E.map (MulAut.conj g).toMonoidHom = F

theorem tabList_eq (l : List P45) : tabList l = l := by
  have : (tab : P45 → P45) = id := funext tab_eq
  rw [tabList, this, List.map_id]

theorem QA45SubgroupConj.trans {E F K : Subgroup ↥QA45.originalSubgroup}
    (h₁ : QA45SubgroupConj E F) (h₂ : QA45SubgroupConj F K) : QA45SubgroupConj E K := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨h, rfl⟩ := h₂
  exact ⟨h * g, (CFSG.GroupTheory.map_conj_map_conj h g E).symm⟩

section ListGroups

variable {L «gens» : List P45}

theorem ListGroupFacts.mem_A (h : ListGroupFacts L «gens») {x : P45} (hx : x ∈ L) :
    x ∈ QA45.originalSubgroup := by
  have := List.all_eq_true.1 h.in_A x hx
  exact (mem_iff_sift QA45 QA45_ok x).2 this

@[expose] def listSubgroup (h : ListGroupFacts L «gens») : Subgroup ↥QA45.originalSubgroup where
  carrier := {x | (x : P45) ∈ L}
  mul_mem' := by
    intro x y hx hy
    have h1 := List.all_eq_true.1 h.mul_closed (x : P45) hx
    have h2 := List.all_eq_true.1 h1 (y : P45) hy
    exact of_decide_eq_true h2
  one_mem' := h.one_mem
  inv_mem' := by
    intro x hx
    have h1 := List.all_eq_true.1 h.inv_closed (x : P45) hx
    exact of_decide_eq_true h1

theorem mem_listSubgroup (h : ListGroupFacts L «gens») (x : ↥QA45.originalSubgroup) :
    x ∈ listSubgroup h ↔ (x : P45) ∈ L := Iff.rfl

theorem card_listSubgroup (h : ListGroupFacts L «gens») : Nat.card (listSubgroup h) = L.length := by
  classical
  let e : listSubgroup h ≃ {p : P45 // p ∈ L.toFinset} :=
    { toFun := fun x => ⟨x.1.1, List.mem_toFinset.2 x.2⟩
      invFun := fun p => ⟨⟨p.1, h.mem_A (List.mem_toFinset.1 p.2)⟩, List.mem_toFinset.1 p.2⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup h.nodup]

theorem closure_le_listSubgroup (h : ListGroupFacts L «gens») {S : Set ↥QA45.originalSubgroup}
    (hS : ∀ x ∈ S, (x : P45) ∈ «gens») : Subgroup.closure S ≤ listSubgroup h := by
  rw [Subgroup.closure_le]
  intro x hx
  have h1 := of_decide_eq_true (List.all_eq_true.1 h.gens_mem (x : P45) (hS x hx))
  exact h1

theorem eq_listSubgroup_of_card (h : ListGroupFacts L «gens») {H : Subgroup ↥QA45.originalSubgroup}
    (hle : H ≤ listSubgroup h) (hc : Nat.card H = L.length) : H = listSubgroup h :=
  Subgroup.eq_of_le_of_card_ge hle (by rw [card_listSubgroup]; exact hc.ge)

end ListGroups

section Named

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a1A" => (⟨alpha1, alpha1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b1A" => (⟨beta1, beta1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : A45)

end Named

theorem commCount_eq (a : P45) :
    commCount a = ((elemsT QA45).filter fun g => g * a = a * g).length := by
  simp [commCount, tab_eq]

theorem length_prodSpan (l : List P45) : (prodSpan l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons g gs ih => simp [prodSpan, ih, pow_succ]; ring

theorem length_T0list : (T0list ()).length = 2 ^ 7 := by
  simp [T0list, tabList, length_prodSpan]

theorem mem_prodSpan_of_mem_closure : ∀ (l : List P45), (∀ x ∈ l, x * x = 1) →
    (∀ a ∈ l, ∀ b ∈ l, a * b = b * a) → ∀ y ∈ Subgroup.closure {x | x ∈ l}, y ∈ prodSpan l
  | [], _, _, y, hy => by
    have h0 : {x : P45 | x ∈ ([] : List P45)} = ∅ := by
      ext
      simp
    rw [h0, Subgroup.closure_empty, Subgroup.mem_bot] at hy
    simp [prodSpan, hy]
  | g :: gs, hsq, hcomm, y, hy => by
    have hsq' : ∀ x ∈ gs, x * x = 1 := fun x hx => hsq x (List.mem_cons_of_mem g hx)
    have hcomm' : ∀ a ∈ gs, ∀ b ∈ gs, a * b = b * a := fun a ha b hb =>
      hcomm a (List.mem_cons_of_mem g ha) b (List.mem_cons_of_mem g hb)
    have ih := mem_prodSpan_of_mem_closure gs hsq' hcomm'
    have hgg : g * g = 1 := hsq g List.mem_cons_self
    have hgH : ∀ h ∈ Subgroup.closure {x | x ∈ gs}, g * h = h * g := by
      have hle : Subgroup.closure {x | x ∈ gs} ≤ Subgroup.centralizer {g} := by
        rw [Subgroup.closure_le]
        intro x hx
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm x (List.mem_cons_of_mem g hx) g List.mem_cons_self)
      intro h hh
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hh)).symm
    have key : ∀ y ∈ Subgroup.closure {x | x ∈ g :: gs},
        y ∈ Subgroup.closure {x | x ∈ gs} ∨ ∃ h ∈ Subgroup.closure {x | x ∈ gs}, y = g * h := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        simp only [Set.mem_setOf_eq, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr ⟨1, one_mem _, by simp⟩
        · exact Or.inl (Subgroup.subset_closure hx)
      | one => exact Or.inl (one_mem _)
      | mul x y _ _ hx hy =>
        rcases hx with hx | ⟨h₁, hh₁, rfl⟩ <;> rcases hy with hy | ⟨h₂, hh₂, rfl⟩
        · exact Or.inl (mul_mem hx hy)
        · refine Or.inr ⟨x * h₂, mul_mem hx hh₂, ?_⟩
          rw [← mul_assoc, ← hgH x hx, mul_assoc]
        · refine Or.inr ⟨h₁ * y, mul_mem hh₁ hy, ?_⟩
          rw [mul_assoc]
        · refine Or.inl ?_
          have : g * h₁ * (g * h₂) = h₁ * h₂ := by
            calc g * h₁ * (g * h₂) = g * (h₁ * g) * h₂ := by simp only [mul_assoc]
              _ = g * (g * h₁) * h₂ := by rw [hgH h₁ hh₁]
              _ = (g * g) * h₁ * h₂ := by simp only [mul_assoc]
              _ = h₁ * h₂ := by rw [hgg, one_mul]
          rw [this]
          exact mul_mem hh₁ hh₂
      | inv x _ hx =>
        rcases hx with hx | ⟨h, hh, rfl⟩
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨h⁻¹, inv_mem hh, ?_⟩
          have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
          rw [mul_inv_rev, hginv, ← hgH h⁻¹ (inv_mem hh)]
    rcases key y hy with hy | ⟨h, hh, rfl⟩
    · exact List.mem_append.2 (Or.inl (ih y hy))
    · exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨h, ih h hh, rfl⟩))

end CFSG.RankThree.GF2n.Parrott
