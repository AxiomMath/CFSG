module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

open Finset

variable {α ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_eq_sum_ite (t : Finset ι) : t.card = ∑ i, if i ∈ t then 1 else 0 := by
  rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter, Finset.univ_inter]

omit [Fintype ι] in
theorem sum_sum_ite_symmDiff (O : Finset α) (γ : α → Finset ι) (i : ι) :
    ∑ B ∈ O, ∑ B' ∈ O, (if i ∈ symmDiff (γ B) (γ B') then 1 else 0) =
      2 * ((O.filter fun B => i ∈ γ B).card * (O.filter fun B => i ∉ γ B).card) := by
  classical
  have h1 : ∀ B ∈ O, (∑ B' ∈ O, (if i ∈ symmDiff (γ B) (γ B') then 1 else 0)) =
      if i ∈ γ B then (O.filter fun B => i ∉ γ B).card
      else (O.filter fun B => i ∈ γ B).card := by
    intro B _
    rw [Finset.sum_boole, Nat.cast_id]
    by_cases h : i ∈ γ B
    · rw [ite_eq_left h]
      congr 1
      ext B'
      simp [Finset.mem_symmDiff, h]
    · rw [ite_eq_right h]
      congr 1
      ext B'
      simp [Finset.mem_symmDiff, h]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul]
  ring

theorem sum_sum_card_symmDiff (O : Finset α) (γ : α → Finset ι) :
    ∑ B ∈ O, ∑ B' ∈ O, (symmDiff (γ B) (γ B')).card =
      ∑ i, 2 * ((O.filter fun B => i ∈ γ B).card * (O.filter fun B => i ∉ γ B).card) := by
  simp_rw [card_eq_sum_ite (symmDiff _ _)]
  rw [Finset.sum_congr rfl fun B _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_sum_ite_symmDiff O γ i

theorem sum_card (O : Finset α) (γ : α → Finset ι) :
    ∑ B ∈ O, (γ B).card = ∑ i, (O.filter fun B => i ∈ γ B).card := by
  simp_rw [card_eq_sum_ite (γ _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_boole, Nat.cast_id]

theorem eq_empty_of_doubleCount (O : Finset α) (γ : α → Finset ι) (hn : Odd O.card)
    {B₀ : α} (h₀ : γ B₀ = ∅)
    (hsym : ∀ i j : ι, (O.filter fun B => i ∈ γ B).card = (O.filter fun B => j ∈ γ B).card)
    (hdist : ∀ B ∈ O, ∑ B' ∈ O, (symmDiff (γ B) (γ B')).card =
      ∑ B' ∈ O, (symmDiff (γ B₀) (γ B')).card) :
    ∀ B ∈ O, γ B = ∅ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · intro B _
    exact Finset.eq_empty_of_isEmpty _
  set a := (O.filter fun B => i₀ ∈ γ B).card with ha
  set b := (O.filter fun B => i₀ ∉ γ B).card with hb
  have hab : a + b = O.card := Finset.card_filter_add_card_filter_not _
  have hai : ∀ i, (O.filter fun B => i ∈ γ B).card = a := fun i => hsym i i₀
  have hbi : ∀ i, (O.filter fun B => i ∉ γ B).card = b := by
    intro i
    have h := Finset.card_filter_add_card_filter_not (s := O) (fun B => i ∈ γ B)
    rw [hai i] at h
    omega
  have hs₀ : ∑ B' ∈ O, (symmDiff (γ B₀) (γ B')).card = Fintype.card ι * a := by
    have e : ∀ s : Finset ι, symmDiff (∅ : Finset ι) s = s := fun s => by
      rw [← Finset.bot_eq_empty, bot_symmDiff]
    simp_rw [h₀, e]
    rw [sum_card, Finset.sum_congr rfl fun i _ => hai i, Finset.sum_const, smul_eq_mul,
      Finset.card_univ]
  have hsum : ∑ B ∈ O, ∑ B' ∈ O, (symmDiff (γ B) (γ B')).card = O.card * (Fintype.card ι * a) := by
    rw [Finset.sum_congr rfl hdist, Finset.sum_const, smul_eq_mul, hs₀]
  rw [sum_sum_card_symmDiff, Finset.sum_congr rfl fun i _ => by rw [hai i, hbi i],
    Finset.sum_const, smul_eq_mul, Finset.card_univ, ← hab] at hsum
  have hk : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have h2 : 2 * (a * b) = (a + b) * a := by
    have h3 : Fintype.card ι * (2 * (a * b)) = Fintype.card ι * ((a + b) * a) := by
      rw [hsum]; ring
    exact Nat.eq_of_mul_eq_mul_left hk h3
  have ha0 : a = 0 := by
    by_contra ha0
    have hpos : 0 < a := Nat.pos_of_ne_zero ha0
    have h4 : 2 * b = a + b := by
      have h5 : a * (2 * b) = a * (a + b) := by rw [← mul_assoc, mul_comm a 2, mul_assoc, h2]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos h5
    have h6 : a = b := by omega
    rw [← hab, h6] at hn
    exact (Nat.not_odd_iff_even.mpr ⟨b, rfl⟩) hn
  intro B hB
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  have h7 : B ∈ O.filter fun B => i ∈ γ B := Finset.mem_filter.mpr ⟨hB, hi⟩
  have h8 : 0 < (O.filter fun B => i ∈ γ B).card := Finset.card_pos.mpr ⟨B, h7⟩
  rw [hai i, ha0] at h8
  exact Nat.lt_irrefl 0 h8

end CFSG.Quasithin.Vol2.Ch10.SecE.C10P02
