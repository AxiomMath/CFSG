module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace AlternatingAutomorphism

open Equiv Equiv.Perm Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem eq_one_of_card_support_le_two {σ : Perm α} (hσ : sign σ = 1) (h : #σ.support ≤ 2) :
    σ = 1 := by
  obtain hs | hs | hs : #σ.support = 0 ∨ #σ.support = 1 ∨ #σ.support = 2 := by omega
  · exact card_support_eq_zero.mp hs
  · exact absurd hs (card_support_ne_one σ)
  · simp [(card_support_eq_two.mp hs).sign_eq] at hσ

theorem eq_or_eq_inv_of_support_eq {c d : Perm α} (hc : c.IsThreeCycle) (hd : d.IsThreeCycle)
    (h : c.support = d.support) : d = c ∨ d = c⁻¹ := by
  obtain ⟨a, ha⟩ := card_pos.mp (hc.card_support ▸ three_pos : 0 < #c.support)
  have key (τ : Perm α) (hτ : τ.IsThreeCycle) (hτs : τ.support = c.support) (hfix : τ (d a) = a) :
      τ * d = 1 := by
    refine eq_one_of_card_support_le_two (by simp [hτ.sign, hd.sign]) ?_
    have : (τ * d).support ⊆ c.support.erase a := fun x hx => mem_erase.mpr
      ⟨fun hxa => mem_support.mp hx (hxa ▸ hfix), by simpa [hτs, ← h] using support_mul_le τ d hx⟩
    simpa [card_erase_of_mem ha, hc.card_support] using card_le_card this
  have hda : d a ∈ ({a, c a, c (c a)} : Finset α) := by
    rw [← hc.support_eq_iff_mem_support.mpr ha, h, apply_mem_support, ← h]
    exact ha
  simp only [mem_insert, mem_singleton] at hda
  rcases hda with hda | hda | hda
  · exact absurd hda (mem_support.mp (h ▸ ha))
  · exact .inl (inv_mul_eq_one.mp (key c⁻¹ hc.inv (support_inv c) (by simp [hda]))).symm
  · refine .inr (eq_inv_of_mul_eq_one_right (key c hc rfl ?_))
    have : (c ^ 3) a = a := by rw [← hc.orderOf, pow_orderOf_eq_one, one_apply]
    simpa [pow_succ, hda] using this

theorem two_le_card_support_inter {c d : Perm α} (hc : c.IsThreeCycle) (hd : d.IsThreeCycle)
    (hcd : (c * d).IsThreeCycle) : 2 ≤ #(c.support ∩ d.support) := by
  have hsub : c.support \ d.support ∪ d.support \ c.support ⊆ (c * d).support := by
    intro x hx
    simp only [mem_union, mem_sdiff, mem_support, not_not] at hx
    rw [mem_support, mul_apply]
    rcases hx with ⟨hcx, hdx⟩ | ⟨hdx, hcx⟩
    · rwa [hdx]
    · exact fun h => hdx (c.injective (h.trans hcx.symm))
  have := card_le_card hsub
  rw [card_union_of_disjoint disjoint_sdiff_sdiff, card_sdiff, card_sdiff, inter_comm,
    hc.card_support, hd.card_support, hcd.card_support] at this
  omega

theorem exists_isThreeCycle_support_eq {s : Finset α} (hs : #s = 3) :
    ∃ c : Perm α, c.IsThreeCycle ∧ c.support = s := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hs
  have h := support_swap_mul_swap (x := x) (y := y) (z := z) (by simp [*])
  exact ⟨_, card_support_eq_three_iff.mp (h ▸ hs), h⟩

theorem isThreeCycle_conj {c : Perm α} (hc : c.IsThreeCycle) (σ : Perm α) :
    (σ * c * σ⁻¹).IsThreeCycle := by
  rw [IsThreeCycle, cycleType_conj]
  exact hc

theorem exists_isThreeCycle_mul_inv {s t : Finset α} (hs : #s = 3) (ht : #t = 3)
    (hst : #(s ∩ t) = 2) : ∃ c d : Perm α, c.support = s ∧ d.support = t ∧
      c.IsThreeCycle ∧ d.IsThreeCycle ∧ (c * d⁻¹).IsThreeCycle := by
  obtain ⟨a, b, hab, he⟩ := card_eq_two.mp hst
  obtain ⟨x, hx⟩ := card_eq_one.mp (show #(s \ t) = 1 by rw [card_sdiff, inter_comm, hst, hs])
  obtain ⟨y, hy⟩ := card_eq_one.mp (show #(t \ s) = 1 by rw [card_sdiff, hst, ht])
  have hs' : s = {x, a, b} := by
    rw [← sdiff_union_inter s t, hx, he]
    exact (insert_eq x _).symm
  have ht' : t = {y, a, b} := by
    rw [← sdiff_union_inter t s, hy, inter_comm, he]
    exact (insert_eq y _).symm
  have hxt : x ∉ t := (mem_sdiff.mp (hx ▸ mem_singleton_self x)).2
  have hys : y ∉ s := (mem_sdiff.mp (hy ▸ mem_singleton_self y)).2
  have hat : a ∈ s ∩ t := he ▸ mem_insert_self a {b}
  have hbt : b ∈ s ∩ t := he ▸ mem_insert_of_mem (mem_singleton_self b)
  have hxa : x ≠ a := fun h => hxt (h ▸ (mem_inter.mp hat).2)
  have hxb : x ≠ b := fun h => hxt (h ▸ (mem_inter.mp hbt).2)
  have hya : y ≠ a := fun h => hys (h ▸ (mem_inter.mp hat).1)
  have hyb : y ≠ b := fun h => hys (h ▸ (mem_inter.mp hbt).1)
  have hxy : x ≠ y := fun h => hxt (h ▸ ht' ▸ mem_insert_self y _)
  have hc := support_swap_mul_swap (x := x) (y := a) (z := b) (by simp [*])
  have hd := support_swap_mul_swap (x := y) (y := a) (z := b) (by simp [*])
  have hcd := support_swap_mul_swap (x := x) (y := a) (z := y) (by simp [*, hya.symm])
  refine ⟨_, _, hc.trans hs'.symm, hd.trans ht'.symm, card_support_eq_three_iff.mp ?_,
    card_support_eq_three_iff.mp ?_, ?_⟩
  · rw [hc, ← hs', hs]
  · rw [hd, ← ht', ht]
  · rw [mul_inv_rev, swap_inv, swap_inv, mul_assoc, ← mul_assoc (swap a b), swap_mul_self,
      one_mul, swap_comm y a, ← card_support_eq_three_iff, hcd]
    simp [*, hya.symm]

end AlternatingAutomorphism

end CFSG
