module

public import CFSG.Permutation.FiveTransitive.ExceptionalThreeSupport
public import CFSG.Permutation.FiveTransitive.FamilyCommutatorAverage
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.ExceptionalThreeAverage

open Equiv
open scoped BigOperators commutatorElement

def eventCount {X : Type*} [Fintype X] [DecidableEq X]
    (g v : Perm X) (a c : X) : ℕ :=
  (g.supportᶜ.filter (fun x => v a = c ∧ v x = a)).card +
  (g.supportᶜ.filter (fun x => v a = x ∧ v c = a)).card

private theorem eventCount_le_one {X : Type*} [Fintype X] [DecidableEq X]
    (g v : Perm X) (a c : X) (hc : c ∈ g.support) : eventCount g v a c ≤ 1 := by
  classical
  let O := g.supportᶜ
  have hfirst : (O.filter (fun x => v a = c ∧ v x = a)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact v.injective ((Finset.mem_filter.mp hx).2.2.trans (Finset.mem_filter.mp hy).2.2.symm)
  have hsecond : (O.filter (fun x => v a = x ∧ v c = a)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact (Finset.mem_filter.mp hx).2.1.symm.trans (Finset.mem_filter.mp hy).2.1
  by_cases h : v a = c
  · have he : O.filter (fun x => v a = x ∧ v c = a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxO := (Finset.mem_filter.mp hx).1
      have hxc : x = c := (Finset.mem_filter.mp hx).2.1.symm.trans h
      subst x
      exact (Finset.mem_compl.mp hxO) hc
    change _ + _ ≤ 1
    rw [show g.supportᶜ = O from rfl, he, Finset.card_empty, add_zero]
    exact hfirst
  · have he : O.filter (fun x => v a = c ∧ v x = a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h (Finset.mem_filter.mp hx).2.1
    change _ + _ ≤ 1
    rw [show g.supportᶜ = O from rfl, he, Finset.card_empty, zero_add]
    exact hsecond

theorem support_ge_min_add_event
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (m : ℕ)
    (hmin : ∀ w : Perm X, w ∈ P → w ≠ 1 → m ≤ w.support.card)
    (hno : ∀ w : Perm X, w ∈ P → orderOf w = 2 → w.support.card ≠ m)
    (g v : Perm X) (hgP : g ∈ P) (hvP : v ∈ P)
    {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hc : c ∈ g.support)
    (ga : g a = b) (gb : g b = c) (gc : g c = a)
    (vb : v b = b) (va : v a ≠ a) (hv3 : v ^ 3 = 1) :
    m + eventCount g v a c ≤ ⁅g, v⁆.support.card := by
  classical
  have hnc : ¬ Commute g v := by
    intro h
    have he := DFunLike.congr_fun h.eq a
    have he' : g (v a) = g a := by simpa only [Perm.mul_apply, ga, vb] using he
    exact va (g.injective he')
  have hmem : ⁅g, v⁆ ∈ P := P.commutator_le_self (Subgroup.commutator_mem_commutator hgP hvP)
  have hne : ⁅g, v⁆ ≠ 1 := fun h => hnc (commutatorElement_eq_one_iff_commute.mp h)
  have hlower := hmin _ hmem hne
  have hupper := eventCount_le_one g v a c hc
  by_cases he : eventCount g v a c = 0
  · omega
  have hex : ∃ x ∈ g.supportᶜ,
      (v a = c ∧ v x = a) ∨ (v a = x ∧ v c = a) := by
    have hpos : 0 < eventCount g v a c := by omega
    unfold eventCount at hpos
    rcases Nat.add_pos_iff_pos_or_pos.mp hpos with hp | hp
    · obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
      exact ⟨x, (Finset.mem_filter.mp hx).1, Or.inl (Finset.mem_filter.mp hx).2⟩
    · obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
      exact ⟨x, (Finset.mem_filter.mp hx).1, Or.inr (Finset.mem_filter.mp hx).2⟩
  obtain ⟨x, hx, horient⟩ := hex
  have gx : g x = x := by simpa only [Finset.mem_compl, Perm.mem_support, not_not] using hx
  have hcube : v (v (v a)) = a := by
    have h := DFunLike.congr_fun hv3 a
    simpa only [pow_succ, pow_zero, Perm.mul_apply, Perm.one_apply] using h
  have hfull : (v a = c ∧ v c = x ∧ v x = a) ∨ (v a = x ∧ v x = c ∧ v c = a) := by
    rcases horient with ⟨hva, hvx⟩ | ⟨hva, hvc⟩
    · refine Or.inl ⟨hva, ?_, hvx⟩
      apply v.injective
      simpa only [hva, hvx] using hcube
    · refine Or.inr ⟨hva, ?_, hvc⟩
      apply v.injective
      simpa only [hva, hvc] using hcube
  have hstrict := ExceptionalThreeSupport.support_gt_min_of_exceptional
    P m hmin hno g v hgP hvP hab hac ga gb gc gx vb hfull
  omega

theorem sum_eventCount_mul
    {T X : Type*} [Fintype T] [Fintype X] [DecidableEq X]
    (g : Perm X) (v : T → Perm X) (a c : X) (D : ℕ)
    (hfirst : ∀ x ∉ g.support, Nat.card {t : T // v t a = c ∧ v t x = a} * D = Nat.card T)
    (hsecond : ∀ x ∉ g.support, Nat.card {t : T // v t a = x ∧ v t c = a} * D = Nat.card T) :
    (∑ t : T, eventCount g (v t) a c) * D =
      2 * Nat.card T * (Fintype.card X - g.support.card) := by
  classical
  simp only [eventCount, Finset.sum_add_distrib, add_mul,
    FamilyCommutatorAverage.sum_card_filter, Finset.sum_mul]
  have he1 : (∑ x ∈ g.supportᶜ, Nat.card {t : T // v t a = c ∧ v t x = a} * D) =
      g.supportᶜ.card * Nat.card T := by
    rw [Finset.sum_congr rfl (fun x hx => hfirst x (Finset.mem_compl.mp hx))]
    simp
  have he2 : (∑ x ∈ g.supportᶜ, Nat.card {t : T // v t a = x ∧ v t c = a} * D) =
      g.supportᶜ.card * Nat.card T := by
    rw [Finset.sum_congr rfl (fun x hx => hsecond x (Finset.mem_compl.mp hx))]
    simp
  rw [he1, he2, Finset.card_compl]
  ring

end FiveTransitive.ExceptionalThreeAverage

end CFSG
