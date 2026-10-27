module

import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open CFSG.LocalAnalysis.ComponentInitial

@[expose] def invCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card

@[expose] def adjSwap {m : ℕ} (i : Fin m) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.swap i.castSucc i.succ

variable {m : ℕ}

private lemma q2cFI_invCount_eq_inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    invCount σ = LinearFlag.inversionCount σ := rfl

private lemma q2cFI_adjSwap_eq (i : Fin m) :
    LinearFlag.adjSwap (m + 1) (i.val + 1) = adjSwap i := by
  rw [LinearFlag.adjSwap_of_lt (by omega) (by omega)]
  simp only [adjSwap]
  congr 1 <;> ext <;> simp

private lemma q2cFI_invCount_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    invCount σ⁻¹ = invCount σ := by
  classical
  refine Finset.card_bij (fun p _ => (σ⁻¹ p.2, σ⁻¹ p.1)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2, by simpa using hp.1⟩
  · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
    simp only [Prod.mk.injEq] at h
    ext <;> simp_all
  · rintro ⟨x, y⟩ hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨(σ y, σ x), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hq.2, by simpa using hq.1⟩
    · simp

theorem adjSwap_mul_self (i : Fin m) : adjSwap i * adjSwap i = 1 := by
  simp [adjSwap]

theorem invCount_mul_adjSwap_of_gt (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m)
    (h : σ i.succ < σ i.castSucc) : invCount (σ * adjSwap i) + 1 = invCount σ := by
  have hleft := (LinearFlag.inversionCount_adjSwap_mul (n := m + 1) (i := i.val + 1)
      (by omega) (by omega) (σ⁻¹)).1 (show σ ⟨i.val + 1, by omega⟩ < σ ⟨i.val, by omega⟩ from h)
  calc
    invCount (σ * adjSwap i) + 1 = invCount ((σ * adjSwap i)⁻¹) + 1 := by
      rw [q2cFI_invCount_inv]
    _ = invCount (adjSwap i * σ⁻¹) + 1 := by simp [mul_inv_rev, adjSwap]
    _ = LinearFlag.inversionCount (LinearFlag.adjSwap (m + 1) (i.val + 1) * σ⁻¹) + 1 := by
      rw [q2cFI_invCount_eq_inversionCount, ← q2cFI_adjSwap_eq i]
    _ = LinearFlag.inversionCount σ⁻¹ := hleft
    _ = invCount σ := by
      rw [← q2cFI_invCount_eq_inversionCount, q2cFI_invCount_inv]

theorem invCount_adjSwap_mul_of_lt (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m)
    (h : σ⁻¹ i.castSucc < σ⁻¹ i.succ) : invCount (adjSwap i * σ) = invCount σ + 1 := by
  have hleft := (LinearFlag.inversionCount_adjSwap_mul (n := m + 1) (i := i.val + 1)
      (by omega) (by omega) σ).2 (show σ⁻¹ ⟨i.val, by omega⟩ < σ⁻¹ ⟨i.val + 1, by omega⟩ from h)
  simpa [← q2cFI_adjSwap_eq i, q2cFI_invCount_eq_inversionCount] using hleft

theorem invCount_adjSwap_mul_of_gt (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m)
    (h : σ⁻¹ i.succ < σ⁻¹ i.castSucc) : invCount (adjSwap i * σ) + 1 = invCount σ := by
  have hleft := (LinearFlag.inversionCount_adjSwap_mul (n := m + 1) (i := i.val + 1)
      (by omega) (by omega) σ).1 (show σ⁻¹ ⟨i.val + 1, by omega⟩ < σ⁻¹ ⟨i.val, by omega⟩ from h)
  simpa [← q2cFI_adjSwap_eq i, q2cFI_invCount_eq_inversionCount] using hleft

theorem invCount_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) : invCount σ⁻¹ = invCount σ :=
  q2cFI_invCount_inv σ

theorem invCount_revPerm (n : ℕ) :
    invCount (Fin.revPerm : Equiv.Perm (Fin n)) = n * (n - 1) / 2 := by
  rw [invCount]
  have h : (Finset.univ.filter fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ Fin.revPerm p.2 < Fin.revPerm p.1) =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) := by
    apply Finset.filter_congr
    intro p _
    constructor
    · exact fun h => h.1
    · intro hlt
      exact ⟨hlt, by simpa using Fin.rev_strictAnti hlt⟩
  rw [h, Fintype.card_product_filter_lt]
  simp [Nat.choose_two_right]

theorem invCount_le (σ : Equiv.Perm (Fin (m + 1))) : invCount σ ≤ (m + 1) * m / 2 := by
  rw [invCount]
  have hsub : (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) =>
      p.1 < p.2 ∧ σ p.2 < σ p.1) ⊆
      (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) => p.1 < p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_product_filter_lt] at hcard
  simpa [Nat.choose_two_right] using hcard

theorem eq_revPerm_of_invCount_eq {σ : Equiv.Perm (Fin (m + 1))}
    (h : invCount σ = (m + 1) * m / 2) : σ = Fin.revPerm := by
  have hcard : (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) =>
      p.1 < p.2 ∧ σ p.2 < σ p.1).card =
      (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) => p.1 < p.2).card := by
    rw [invCount] at h
    rw [h, Fintype.card_product_filter_lt]
    simp [Nat.choose_two_right]
  have heq : (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) =>
      p.1 < p.2 ∧ σ p.2 < σ p.1) =
      (Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) => p.1 < p.2) := by
    apply Finset.eq_of_subset_of_card_le _ hcard.ge
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  have hanti : StrictAnti σ := by
    intro a b hab
    have hmem : (a, b) ∈ Finset.univ.filter fun p : Fin (m + 1) × Fin (m + 1) =>
        p.1 < p.2 ∧ σ p.2 < σ p.1 := by
      rw [heq]
      simp [hab]
    simpa using (Finset.mem_filter.mp hmem).2.2
  have hrev : StrictAnti (Fin.revPerm : Fin (m + 1) → Fin (m + 1)) := by
    intro a b hab
    simpa [Fin.revPerm_apply] using Fin.rev_strictAnti hab
  have hcomp : (σ : Fin (m + 1) → Fin (m + 1)) ∘
      (Fin.revPerm : Fin (m + 1) → Fin (m + 1)) = id := by
    apply StrictMono.eq_id
    exact hanti.comp hrev
  apply Equiv.ext
  intro x
  have hx := congrFun hcomp (Fin.revPerm x)
  simpa using hx

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
