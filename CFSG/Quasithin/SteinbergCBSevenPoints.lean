module

public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Perm.ClosureSwap
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.SteinbergCB

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

@[expose] def sevenP : Subgroup (Perm (Fin 7)) :=
  closure {swap 0 1, swap 2 3, swap 4 5, swap 2 4 * swap 3 5}

@[expose] def sevenA : Subgroup (Perm (Fin 7)) :=
  MulAction.stabilizer (Perm (Fin 7)) ({2, 3, 4, 5} : Finset (Fin 7))

@[expose] def sevenB : Subgroup (Perm (Fin 7)) :=
  MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) ⊓
    MulAction.stabilizer (Perm (Fin 7)) ({{0, 1}, {2, 3}, {4, 5}} : Finset (Finset (Fin 7)))

theorem mem_sevenA {g : Perm (Fin 7)} :
    g ∈ sevenA ↔ g • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} :=
  MulAction.mem_stabilizer_iff

theorem mem_sevenB {g : Perm (Fin 7)} :
    g ∈ sevenB ↔ g • (6 : Fin 7) = 6 ∧
      g • ({{0, 1}, {2, 3}, {4, 5}} : Finset (Finset (Fin 7))) = {{0, 1}, {2, 3}, {4, 5}} := by
  rw [sevenB, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]

theorem card_filter_sevenA : (Finset.univ.filter fun g : Perm (Fin 7) =>
    g • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5}).card = 144 := by
  decide +kernel

theorem card_filter_sevenB : (Finset.univ.filter fun g : Perm (Fin 7) => g • (6 : Fin 7) = 6 ∧
    g • ({{0, 1}, {2, 3}, {4, 5}} : Finset (Finset (Fin 7))) = {{0, 1}, {2, 3}, {4, 5}}).card =
      48 := by
  decide +kernel

@[expose] def sevenWord (u : Bool × Bool × Bool × Bool) : Perm (Fin 7) :=
  (if u.1 then swap 0 1 else 1) * (if u.2.1 then swap 2 3 else 1) *
    (if u.2.2.1 then swap 4 5 else 1) * (if u.2.2.2 then swap 2 4 * swap 3 5 else 1)

@[expose] def sevenCond (g : Perm (Fin 7)) : Prop :=
  g • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} ∧ g • (6 : Fin 7) = 6 ∧
    g • ({{0, 1}, {2, 3}, {4, 5}} : Finset (Finset (Fin 7))) = {{0, 1}, {2, 3}, {4, 5}}

instance : DecidablePred sevenCond := fun g => by
  unfold sevenCond
  infer_instance

theorem card_filter_sevenCond : (Finset.univ.filter sevenCond).card = 16 := by
  decide +kernel

theorem sevenCond_sevenWord : ∀ u, sevenCond (sevenWord u) := by
  decide +kernel

theorem sevenWord_injective : Function.Injective sevenWord := by
  unfold Function.Injective
  decide +kernel

theorem exists_sevenWord_of_sevenCond {g : Perm (Fin 7)} (hg : sevenCond g) :
    ∃ u, g = sevenWord u := by
  have himage : Finset.univ.image sevenWord = Finset.univ.filter sevenCond := by
    refine Finset.eq_of_subset_of_card_le (fun g hg => ?_) ?_
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hg
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, sevenCond_sevenWord u⟩
    · rw [card_filter_sevenCond, Finset.card_image_of_injective _ sevenWord_injective]
      rfl
  have : g ∈ Finset.univ.image sevenWord := by
    rw [himage]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩
  obtain ⟨u, -, hu⟩ := Finset.mem_image.1 this
  exact ⟨u, hu.symm⟩

theorem sevenCond_swap01 : sevenCond (swap 0 1) := by
  unfold sevenCond
  decide +kernel

theorem sevenCond_swap23 : sevenCond (swap 2 3) := by
  unfold sevenCond
  decide +kernel

theorem sevenCond_swap45 : sevenCond (swap 4 5) := by
  unfold sevenCond
  decide +kernel

theorem sevenCond_flip : sevenCond (swap 2 4 * swap 3 5) := by
  unfold sevenCond
  decide +kernel

theorem swap06_fix :
    (swap 0 6 : Perm (Fin 7)) • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} := by
  decide +kernel

theorem swap24_fix :
    (swap 2 4 : Perm (Fin 7)) • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} := by
  decide +kernel

theorem swap25_fix :
    (swap 2 5 : Perm (Fin 7)) • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} := by
  decide +kernel

theorem flip_mem_sevenB : (swap 0 2 * swap 1 3 : Perm (Fin 7)) • (6 : Fin 7) = 6 ∧
    (swap 0 2 * swap 1 3 : Perm (Fin 7)) • ({{0, 1}, {2, 3}, {4, 5}} : Finset (Finset (Fin 7))) =
      {{0, 1}, {2, 3}, {4, 5}} := by
  decide +kernel

theorem swap_two_six_eq : (swap 2 6 : Perm (Fin 7)) =
    (swap 0 2 * swap 1 3) * swap 0 6 * (swap 0 2 * swap 1 3)⁻¹ := by
  decide

theorem nat_card_sevenA : Nat.card sevenA = 144 := by
  rw [← card_filter_sevenA, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_sevenA)

theorem nat_card_sevenB : Nat.card sevenB = 48 := by
  rw [← card_filter_sevenB, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_sevenB)

theorem isSolvable_sevenB : Group.IsSolvable sevenB :=
  CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [nat_card_sevenB]; norm_num)

theorem isSolvable_sevenA : Group.IsSolvable sevenA := by
  set p : Fin 7 → Prop := fun x => x ∈ ({2, 3, 4, 5} : Finset (Fin 7)) with hp
  have h1 : Group.IsSolvable (Perm {a // p a}) := by
    refine CFSG.GroupTheory.groups_order_below_sixty_solvable ?_
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  have h2 : Group.IsSolvable (Perm {a // ¬ p a}) := by
    refine CFSG.GroupTheory.groups_order_below_sixty_solvable ?_
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  have hle : sevenA ≤ (subtypeCongrHom p).range := by
    intro g hg
    have hgS := mem_sevenA.1 hg
    have hpg : ∀ x, p (g x) ↔ p x := by
      intro x
      simp only [hp]
      constructor
      · intro h
        have : g x ∈ g • ({2, 3, 4, 5} : Finset (Fin 7)) := by rw [hgS]; exact h
        rw [Finset.mem_smul_finset] at this
        obtain ⟨y, hy, hyx⟩ := this
        rw [Perm.smul_def] at hyx
        rw [← g.injective hyx]
        exact hy
      · intro h
        rw [← hgS]
        exact Finset.smul_mem_smul_finset h
    have hnpg : ∀ x, ¬ p (g x) ↔ ¬ p x := fun x => not_congr (hpg x)
    refine ⟨(g.subtypePerm hpg, g.subtypePerm hnpg), ?_⟩
    ext x
    by_cases hx : p x
    · simp [subtypeCongrHom_apply, Perm.subtypeCongr.left_apply _ _ hx]
    · simp [subtypeCongrHom_apply, Perm.subtypeCongr.right_apply _ _ hx]
  have h3 : Group.IsSolvable (subtypeCongrHom p).range :=
    Group.isSolvable_of_surjective (subtypeCongrHom p).rangeRestrict_surjective
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem sevenA_inf_sevenB : sevenA ⊓ sevenB = sevenP := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hA, hB⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨h6, hpairs⟩ := mem_sevenB.1 hB
    obtain ⟨u, rfl⟩ := exists_sevenWord_of_sevenCond ⟨mem_sevenA.1 hA, h6, hpairs⟩
    have hm : ∀ s ∈ ({swap 0 1, swap 2 3, swap 4 5, swap 2 4 * swap 3 5} :
        Set (Perm (Fin 7))), s ∈ sevenP := fun s hs => subset_closure hs
    obtain ⟨a, b, c, d⟩ := u
    refine sevenP.mul_mem (sevenP.mul_mem (sevenP.mul_mem ?_ ?_) ?_) ?_
    · split_ifs
      · exact hm _ (by simp)
      · exact sevenP.one_mem
    · split_ifs
      · exact hm _ (by simp)
      · exact sevenP.one_mem
    · split_ifs
      · exact hm _ (by simp)
      · exact sevenP.one_mem
    · split_ifs
      · exact hm _ (by simp)
      · exact sevenP.one_mem
  · rw [sevenP, closure_le]
    intro g hg
    have hc : sevenCond g := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact sevenCond_swap01
      · exact sevenCond_swap23
      · exact sevenCond_swap45
      · exact sevenCond_flip
    obtain ⟨h1, h2, h3⟩ := hc
    exact Subgroup.mem_inf.2 ⟨mem_sevenA.2 h1, mem_sevenB.2 ⟨h2, h3⟩⟩

theorem sevenA_sup_sevenB : sevenA ⊔ sevenB = ⊤ := by
  set S : Set (Perm (Fin 7)) :=
    {swap 0 6, swap 0 1, swap 2 3, swap 2 4, swap 2 5, swap 2 6} with hS
  have hSswap : ∀ σ ∈ S, σ.IsSwap := by
    intro σ hσ
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, by decide, rfl⟩
  have hmem : ∀ σ ∈ S, σ ∈ closure S := fun σ hσ => subset_closure hσ
  have hword : ∀ y : Fin 7, ∃ g ∈ closure S, g 0 = y := by
    have m06 := hmem (swap 0 6) (by simp [hS])
    have m01 := hmem (swap 0 1) (by simp [hS])
    have m23 := hmem (swap 2 3) (by simp [hS])
    have m24 := hmem (swap 2 4) (by simp [hS])
    have m25 := hmem (swap 2 5) (by simp [hS])
    have m26 := hmem (swap 2 6) (by simp [hS])
    intro y
    fin_cases y
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨_, m01, by decide⟩
    · exact ⟨_, mul_mem m26 m06, by decide⟩
    · exact ⟨_, mul_mem (mul_mem m23 m26) m06, by decide⟩
    · exact ⟨_, mul_mem (mul_mem m24 m26) m06, by decide⟩
    · exact ⟨_, mul_mem (mul_mem m25 m26) m06, by decide⟩
    · exact ⟨_, m06, by decide⟩
  have : MulAction.IsPretransitive (closure S) (Fin 7) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg, hgx⟩ := hword x
    obtain ⟨h, hh, hhy⟩ := hword y
    refine ⟨⟨h * g⁻¹, mul_mem hh (inv_mem hg)⟩, ?_⟩
    rw [Subgroup.mk_smul, Perm.smul_def, Perm.mul_apply, Perm.inv_eq_iff_eq.2 hgx.symm, hhy]
  have htop := closure_of_isSwap_of_isPretransitive hSswap
  rw [eq_top_iff, ← htop, closure_le]
  intro σ hσ
  simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  have hA06 : (swap 0 6 : Perm (Fin 7)) ∈ sevenA ⊔ sevenB :=
    Subgroup.mem_sup_left (mem_sevenA.2 swap06_fix)
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hA06
  · exact Subgroup.mem_sup_left (mem_sevenA.2 sevenCond_swap01.1)
  · exact Subgroup.mem_sup_left (mem_sevenA.2 sevenCond_swap23.1)
  · exact Subgroup.mem_sup_left (mem_sevenA.2 swap24_fix)
  · exact Subgroup.mem_sup_left (mem_sevenA.2 swap25_fix)
  · rw [swap_two_six_eq]
    have hb : (swap 0 2 * swap 1 3 : Perm (Fin 7)) ∈ sevenA ⊔ sevenB :=
      Subgroup.mem_sup_right (mem_sevenB.2 flip_mem_sevenB)
    exact mul_mem (mul_mem hb hA06) (inv_mem hb)

theorem A7_two_solvable_overgroups_generate_S7 :
    Group.IsSolvable sevenA ∧ Group.IsSolvable sevenB ∧ Nat.card sevenA = 144 ∧
      Nat.card sevenB = 48 ∧ sevenA ⊓ sevenB = sevenP ∧ sevenA ⊔ sevenB = ⊤ :=
  ⟨isSolvable_sevenA, isSolvable_sevenB, nat_card_sevenA, nat_card_sevenB, sevenA_inf_sevenB,
    sevenA_sup_sevenB⟩

end CFSG.Quasithin.SteinbergCB
