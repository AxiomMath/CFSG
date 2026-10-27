module

public import CFSG.RankThree.GF2n.Parrott.QA45ListGroups
public import CFSG.GroupTheory.ConjClassCover

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem qa45_involution_centralizers :
    Nat.card (Subgroup.centralizer ({tA} : Set A45)) = 1152 ∧
    Nat.card (Subgroup.centralizer ({uA * tA} : Set A45)) = 192 ∧
    Nat.card (Subgroup.centralizer ({vA} : Set A45)) = 96 ∧
    Nat.card (Subgroup.centralizer ({uA * vA} : Set A45)) = 1440 := by
  have hut : u * t ∈ QA45.originalSubgroup := QA45.originalSubgroup.mul_mem u_mem_A t_mem_A
  have huv : u * v ∈ QA45.originalSubgroup := QA45.originalSubgroup.mul_mem u_mem_A v_mem_A
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [card_centralizer_QA45_eq_filter t t_mem_A]
    exact Certificates.certificate946005.centralizer_t
  · have h := card_centralizer_QA45_eq_filter (u * t) hut
    change Nat.card (Subgroup.centralizer ({⟨u * t, hut⟩} : Set A45)) = 192
    rw [h, ← commCount_eq]
    exact qa45L1Facts.centralizer_ut
  · rw [card_centralizer_QA45_eq_filter v v_mem_A]
    exact Certificates.certificate946005.centralizer_v
  · have h := card_centralizer_QA45_eq_filter (u * v) huv
    change Nat.card (Subgroup.centralizer ({⟨u * v, huv⟩} : Set A45)) = 1440
    rw [h, ← commCount_eq]
    exact qa45L1Facts.centralizer_uv

theorem qa45_involution_classes :
    ∀ x : A45, orderOf x = 2 →
      IsConj x tA ∨ IsConj x (uA * tA) ∨ IsConj x vA ∨ IsConj x (uA * vA) := by
  obtain ⟨hC1, hC2, hC3, hC4⟩ := qa45_involution_centralizers
  have hA : Nat.card A45 = 51840 := card_QA45
  let s : Set A45 := {x | x * x = 1 ∧ x ≠ 1}
  have hs : ∀ x y : A45, IsConj x y → y ∈ s → x ∈ s := by
    intro x y hxy hy
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, fun h1 => hy2 (isConj_one_right.1 (h1 ▸ hxy))⟩
    have h2 : IsConj (x ^ 2) (y ^ 2) := hxy.pow 2
    rw [sq y, hy1] at h2
    rw [← sq]
    exact isConj_one_left.1 h2
  have hmem_s : ∀ x : A45, orderOf x = 2 → x ∈ s := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [← sq, ← hx]
      exact pow_orderOf_eq_one x
    · intro h1
      rw [h1, orderOf_one] at hx
      omega
  have hscard : s.ncard = 891 := by
    rw [← Nat.card_coe_set_eq, ← qa45L1Facts.card_involutions, involutionCount]
    have h := card_filter QA45 QA45_ok (p := fun g : Equiv.Perm (Fin 45) => g * g = 1 ∧ g ≠ 1)
    rw [← h]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    simp only [s, Set.mem_setOf_eq, ne_eq, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one]
  let r : Fin 4 → A45 := ![tA, uA * tA, vA, uA * vA]
  have hcard : ∀ i, Nat.card (Subgroup.centralizer ({r i} : Set A45)) =
      ![1152, 192, 96, 1440] i := by
    intro i
    fin_cases i
    · exact hC1
    · exact hC2
    · exact hC3
    · exact hC4
  have hr1 : ∀ i, r i ≠ 1 := by
    intro i
    refine CFSG.GroupTheory.ne_one_of_card_centralizer_ne ?_
    rw [hcard i, hA]
    revert i
    decide
  have hut : Commute tA uA := Subtype.ext t_commute_u
  have huv : Commute uA vA := Subtype.ext u_commute_v
  have htt : tA * tA = 1 := Subtype.ext t_sq
  have huu : uA * uA = 1 := Subtype.ext u_sq
  have hvv : vA * vA = 1 := Subtype.ext v_sq
  have hr : ∀ i, r i ∈ s := by
    intro i
    refine ⟨?_, hr1 i⟩
    fin_cases i
    · exact htt
    · show (uA * tA) * (uA * tA) = 1
      rw [Commute.mul_mul_mul_comm hut uA tA, huu, htt, one_mul]
    · exact hvv
    · show (uA * vA) * (uA * vA) = 1
      rw [Commute.mul_mul_mul_comm huv.symm uA vA, huu, hvv, one_mul]
  have hne : ∀ i j, i ≠ j → Nat.card (Subgroup.centralizer ({r i} : Set A45)) ≠
      Nat.card (Subgroup.centralizer ({r j} : Set A45)) := by
    intro i j hij
    rw [hcard, hcard]
    revert i j
    decide
  have hsum : ∑ i, Nat.card A45 / Nat.card (Subgroup.centralizer ({r i} : Set A45)) =
      s.ncard := by
    simp only [hcard, hA, hscard, Fin.sum_univ_four]
    norm_num
  intro x hx
  obtain ⟨i, hi⟩ := CFSG.GroupTheory.exists_isConj_of_sum_eq r s hs hr hne hsum x (hmem_s x hx)
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (Or.inl hi))
  · exact Or.inr (Or.inr (Or.inr hi))

end CFSG.RankThree.GF2n.Parrott
