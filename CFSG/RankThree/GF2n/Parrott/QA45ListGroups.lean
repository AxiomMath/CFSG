
module

public import CFSG.RankThree.GF2n.Parrott.QA45ListGroupsBase

public import Certificates.Certificate946017
public import CFSG.RankThree.GF2n.Parrott.SylowHFacts
public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree
public import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups
open CFSG.Sporadic.Schreier (tab tab_eq)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup

local notation "P45" => Equiv.Perm (Fin 45)

theorem length_Slist : (Slist ()).length = 2 ^ 4 := by
  simp [Slist, tabList, length_prodSpan, Sgens]

theorem length_E3list : (E3list ()).length = 2 ^ 4 := by
  simp [E3list, tabList, length_prodSpan, E3gens]

theorem length_E1list : (E1list ()).length = 2 ^ 4 := by
  simp [E1list, tabList, length_prodSpan, E1gens]

theorem length_E2list : (E2list ()).length = 2 ^ 4 := by
  simp [E2list, tabList, length_prodSpan, E2gens]

theorem pairwiseCommB_of_forall {l : List P45}
    (h : ∀ a ∈ l, ∀ b ∈ l, a * b = b * a) : pairwiseCommB l = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [pairwiseCommB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun b hb => h a (List.mem_cons_self) b (List.mem_cons_of_mem a hb),
      ih fun x hx y hy => h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)⟩

theorem e16Check_spec (h : e16Check () = true) :
    ∀ l ∈ (involutionsOf (T0list ())).sublistsLen 4, pairwiseCommB l = true →
      (prodSpan l).Nodup →
      subsetB (prodSpan l) (Slist ()) = true ∨ subsetB (prodSpan l) (E3list ()) = true ∨
        subsetB (prodSpan l) (E1list ()) = true ∨ subsetB (prodSpan l) (E2list ()) = true := by
  intro l hl hcomm hnd
  have h1 := List.all_eq_true.1 h l hl
  simp only [hcomm, tabList_eq, hnd, decide_true, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at h1
  simpa [or_assoc] using h1

theorem invCentralizerB_spec {T gs L : List P45} (h : invCentralizerB T gs L = true) :
    ∀ c ∈ T, c * c = 1 → (∀ x ∈ gs, c * x = x * c) → c ∈ L := by
  intro c hc hsq hx
  by_contra hnot
  have h1 := List.all_eq_true.1 h c hc
  have hall : (gs.all fun x => decide (c * x = x * c)) = true :=
    List.all_eq_true.2 fun x hxm => decide_eq_true (hx x hxm)
  have hcL : decide (c ∈ L) = false := decide_eq_false hnot
  simp [hall, hcL, hsq] at h1

theorem e16CentralizerCheck_spec (h : e16CentralizerCheck () = true) :
    (∀ c ∈ T0list (), c * c = 1 → (∀ x ∈ Sgens, c * x = x * c) → c ∈ Slist ()) ∧
    (∀ c ∈ T0list (), c * c = 1 → (∀ x ∈ E3gens, c * x = x * c) → c ∈ E3list ()) ∧
    (∀ c ∈ T0list (), c * c = 1 → (∀ x ∈ E1gens, c * x = x * c) → c ∈ E1list ()) ∧
    (∀ c ∈ T0list (), c * c = 1 → (∀ x ∈ E2gens, c * x = x * c) → c ∈ E2list ()) := by
  simp only [e16CentralizerCheck, Bool.and_eq_true, tabList_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨invCentralizerB_spec h1, invCentralizerB_spec h2, invCentralizerB_spec h3,
    invCentralizerB_spec h4⟩

theorem meetUtB_spec {A S X : List P45} (h : meetUtB A S X = true) :
    ∃ z ∈ X, z ≠ 1 ∧ z ∈ S ∧ ∃ c ∈ A, c * z * c⁻¹ = u * t := by
  simp only [meetUtB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, tab_eq] at h
  obtain ⟨z, hzX, ⟨hz1, hzS⟩, c, hcA, hc⟩ := h
  exact ⟨z, hzX, hz1, hzS, c, hcA, hc⟩

theorem e16MeetCheck_spec (h : e16MeetCheck () = true) :
    (∃ z ∈ Slist (), z ≠ 1 ∧ z ∈ Slist () ∧ ∃ c ∈ elemsT QA45, c * z * c⁻¹ = u * t) ∧
    (∃ z ∈ E3list (), z ≠ 1 ∧ z ∈ Slist () ∧ ∃ c ∈ elemsT QA45, c * z * c⁻¹ = u * t) ∧
    (∃ z ∈ E1list (), z ≠ 1 ∧ z ∈ Slist () ∧ ∃ c ∈ elemsT QA45, c * z * c⁻¹ = u * t) ∧
    (∃ z ∈ E2list (), z ≠ 1 ∧ z ∈ Slist () ∧ ∃ c ∈ elemsT QA45, c * z * c⁻¹ = u * t) := by
  simp only [e16MeetCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨meetUtB_spec h1, meetUtB_spec h2, meetUtB_spec h3, meetUtB_spec h4⟩

theorem qa45L1Facts : QA45L1Facts :=
  Certificates.certificate946017

section Named

theorem sylowTwoQA45_eq_listSubgroup :
    sylowTwoQA45 = listSubgroup Certificates.certificate946017.t0_group := by
  refine eq_listSubgroup_of_card _ ?_ ?_
  · unfold sylowTwoQA45
    refine closure_le_listSubgroup _ fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [T0gens]
  · rw [card_sylowTwoQA45, length_T0list]

theorem mem_sylowTwoQA45_iff (x : ↥QA45.originalSubgroup) :
    x ∈ sylowTwoQA45 ↔ (x : Equiv.Perm (Fin 45)) ∈ T0list () := by
  rw [sylowTwoQA45_eq_listSubgroup]
  exact Iff.rfl

theorem sQA45_eq_listSubgroup : sQA45 = listSubgroup Certificates.certificate946017.s_group := by
  refine eq_listSubgroup_of_card _ ?_ ?_
  · unfold sQA45
    refine closure_le_listSubgroup _ fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [Sgens]
  · rw [card_sQA45, length_Slist]

theorem mem_sQA45_iff (x : A45) : x ∈ sQA45 ↔ (x : Equiv.Perm (Fin 45)) ∈ Slist () := by
  rw [sQA45_eq_listSubgroup]
  exact Iff.rfl

theorem eUVQA45_eq_listSubgroup : eUVQA45 = listSubgroup Certificates.certificate946017.e3_group := by
  refine eq_listSubgroup_of_card _ ?_ ?_
  · unfold eUVQA45
    refine closure_le_listSubgroup _ fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [E3gens]
  · rw [card_eUVQA45, length_E3list]

theorem eVQA45_eq_listSubgroup : eVQA45 = listSubgroup Certificates.certificate946017.e1_group := by
  refine eq_listSubgroup_of_card _ ?_ ?_
  · unfold eVQA45
    refine closure_le_listSubgroup _ fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [E1gens]
  · rw [card_eVQA45, length_E1list]

theorem eVAQA45_eq_listSubgroup : eVAQA45 = listSubgroup Certificates.certificate946017.e2_group := by
  refine eq_listSubgroup_of_card _ ?_ ?_
  · unfold eVAQA45
    refine closure_le_listSubgroup _ fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [E2gens]
  · rw [card_eVAQA45, length_E2list]

end Named

end CFSG.RankThree.GF2n.Parrott
