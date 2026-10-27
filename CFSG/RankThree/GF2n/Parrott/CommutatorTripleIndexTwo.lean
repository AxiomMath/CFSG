module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GF2n.Parrott

open scoped commutatorElement

variable {Q : Type*} [Group Q]

private theorem mul_commutator_comm_of_mem_of_not_mem {P : Subgroup Q} (hP : P.index = 2)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hsq : ∀ a ∈ P, a * a = 1)
    {b c : Q} (hb : b ∈ P) (hc : c ∉ P) (a : Q) :
    a * ⁅b, c⁆ = ⁅b, c⁆ * a := by
  have hnorm : P.Normal := Subgroup.normal_of_index_eq_two hP
  have hw : c * b * c⁻¹ ∈ P := hnorm.conj_mem b hb c
  have hcc : c * c ∈ P := Subgroup.mul_self_mem_of_index_two hP c
  have hwinv : (c * b * c⁻¹)⁻¹ = c * b * c⁻¹ := inv_eq_of_mul_eq_one_right (hsq _ hw)
  have hd : ⁅b, c⁆ = b * (c * b * c⁻¹) := by
    rw [commutatorElement_def]
    calc b * c * b⁻¹ * c⁻¹ = b * (c * b * c⁻¹)⁻¹ := by group
      _ = b * (c * b * c⁻¹) := by rw [hwinv]
  have hdP : ⁅b, c⁆ ∈ P := by
    rw [hd]
    exact P.mul_mem hb hw
  by_cases ha : a ∈ P
  · exact hcomm a ha _ hdP
  · have hp : a * c⁻¹ ∈ P := by
      rw [Subgroup.mul_mem_iff_of_index_two hP]
      exact iff_of_false ha (fun h => hc ((Subgroup.inv_mem_iff P).mp h))
    obtain ⟨p, hpP, rfl⟩ : ∃ p ∈ P, a = p * c := ⟨a * c⁻¹, hp, by group⟩
    have e1 : c * b * c = (c * b * c⁻¹) * (c * c) := by group
    have e2 : (c * c) * b = b * (c * c) := hcomm _ hcc b hb
    have e3' : ∀ u ∈ P, p * u * b = b * u * p := by
      intro u hu
      calc p * u * b = p * (u * b) := mul_assoc _ _ _
        _ = p * (b * u) := by rw [hcomm u hu b hb]
        _ = (p * b) * u := (mul_assoc _ _ _).symm
        _ = (b * p) * u := by rw [hcomm p hpP b hb]
        _ = b * (p * u) := mul_assoc _ _ _
        _ = b * (u * p) := by rw [hcomm p hpP u hu]
        _ = b * u * p := (mul_assoc _ _ _).symm
    have e3 : p * (c * b * c⁻¹) * b = b * (c * b * c⁻¹) * p := e3' _ hw
    rw [hd]
    calc p * c * (b * (c * b * c⁻¹))
        = p * (c * b * c) * b * c⁻¹ := by group
      _ = p * ((c * b * c⁻¹) * (c * c)) * b * c⁻¹ := by rw [e1]
      _ = p * (c * b * c⁻¹) * ((c * c) * b) * c⁻¹ := by group
      _ = p * (c * b * c⁻¹) * (b * (c * c)) * c⁻¹ := by rw [e2]
      _ = (p * (c * b * c⁻¹) * b) * c := by group
      _ = (b * (c * b * c⁻¹) * p) * c := by rw [e3]
      _ = b * (c * b * c⁻¹) * (p * c) := by group

theorem commutator_triple_eq_one_of_index_two_elemAbelian (P : Subgroup Q) (hP : P.index = 2)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hsq : ∀ a ∈ P, a * a = 1) :
    ∀ a b c : Q, ⁅a, ⁅b, c⁆⁆ = 1 := by
  intro a b c
  rw [commutatorElement_eq_one_iff_mul_comm]
  by_cases hb : b ∈ P <;> by_cases hc : c ∈ P
  · have h1 : ⁅b, c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hcomm b hb c hc)
    rw [h1, mul_one, one_mul]
  · exact mul_commutator_comm_of_mem_of_not_mem hP hcomm hsq hb hc a
  · have h1 := mul_commutator_comm_of_mem_of_not_mem hP hcomm hsq hc hb a
    have h2 : Commute a ⁅c, b⁆ := h1
    have h3 := h2.inv_right
    rw [commutatorElement_inv] at h3
    exact h3
  · have hp : b * c⁻¹ ∈ P := by
      rw [Subgroup.mul_mem_iff_of_index_two hP]
      exact iff_of_false hb (fun h => hc ((Subgroup.inv_mem_iff P).mp h))
    obtain ⟨p, hpP, rfl⟩ : ∃ p ∈ P, b = p * c := ⟨b * c⁻¹, hp, by group⟩
    have h1 : ⁅p * c, c⁆ = ⁅p, c⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact mul_commutator_comm_of_mem_of_not_mem hP hcomm hsq hpP hc a

end CFSG.RankThree.GF2n.Parrott
