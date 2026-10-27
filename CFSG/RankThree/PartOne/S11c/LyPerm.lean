module

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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.LyPerm

open Equiv Equiv.Perm

variable {α : Type} [Fintype α] [DecidableEq α]

def fixF (g : Perm α) : Finset α := Finset.univ.filter fun x => g x = x

theorem mem_fixF {g : Perm α} {x : α} : x ∈ fixF g ↔ g x = x := by
  simp [fixF]

theorem card_fix_modEq {g h : Perm α} (hgh : g * h = h * g) {p n : ℕ} [Fact p.Prime]
    (hh : h ^ (p ^ n) = 1) :
    (fixF g).card ≡ (fixF g ∩ fixF h).card [MOD p] := by
  classical
  have hP : ∀ x, g x = x → g (h x) = h x := by
    intro x hx
    have := congrArg (fun π : Perm α => π x) hgh
    simp only [Perm.mul_apply] at this
    rw [this, hx]
  let f : Function.End {x // g x = x} := fun x => ⟨h x, hP x.1 x.2⟩
  have hfk : ∀ (k : ℕ) (x : {x // g x = x}),
      (((f ^ k : Function.End {x // g x = x}) x : {x // g x = x}) : α) = (h ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Perm.mul_apply]
      exact ih (f x)
  have hf1 : f ^ p ^ n = 1 := by
    funext x
    apply Subtype.ext
    rw [hfk, hh]
    rfl
  have h1 := Equiv.Perm.card_fixedPoints_modEq (α := {x // g x = x}) (f := f) (p := p) (n := n) hf1
  have hc1 : Fintype.card {x // g x = x} = (fixF g).card := by
    rw [Fintype.card_subtype]
    rfl
  have hc2 : Fintype.card (Function.fixedPoints f) = (fixF g ∩ fixF h).card := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun x => ⟨x.1.1, by
          rw [Finset.mem_inter, mem_fixF, mem_fixF]
          exact ⟨x.1.2, congrArg Subtype.val x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, mem_fixF.mp (Finset.mem_inter.mp y.2).1⟩, Subtype.ext
          (mem_fixF.mp (Finset.mem_inter.mp y.2).2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hc1, hc2] at h1
  exact h1


theorem card_fix_five {σ : Perm (Fin 11)} (hσ : orderOf σ = 5) :
    (fixF σ).card = 1 ∨ (fixF σ).card = 6 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := card_fix_modEq (g := (1 : Perm (Fin 11))) (h := σ) (by simp) (p := 5) (n := 1)
    (by rw [pow_one, ← hσ]; exact pow_orderOf_eq_one σ)
  have h1 : (fixF (1 : Perm (Fin 11))).card = 11 := by simp [fixF]
  have h2 : fixF (1 : Perm (Fin 11)) ∩ fixF σ = fixF σ := by
    ext x
    simp [mem_fixF]
  rw [h1, h2] at h
  have hle : (fixF σ).card ≤ 11 := by
    have := Finset.card_le_univ (fixF σ)
    simpa using this
  have hne : (fixF σ).card ≠ 11 := by
    intro h11
    have hall : fixF σ = Finset.univ := Finset.eq_univ_of_card _ (by simpa using h11)
    have : σ = 1 := Equiv.ext fun x => by
      have := mem_fixF.mp (hall ▸ Finset.mem_univ x)
      simpa using this
    rw [this, orderOf_one] at hσ
    omega
  unfold Nat.ModEq at h
  omega

theorem card_fixed_eq_three_or_seven {u : Perm (Fin 11)} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hs : sign u = 1) : (fixF u).card = 3 ∨ (fixF u).card = 7 := by
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hall : ∀ m ∈ u.cycleType, m = 2 := fun m hm => by
    have h1 := dvd_of_mem_cycleType hm
    rw [hord] at h1
    have h2 := two_le_of_mem_cycleType hm
    exact ((Nat.dvd_prime Nat.prime_two).mp h1).resolve_left (by omega)
  have hrep : u.cycleType = Multiset.replicate (Multiset.card u.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hall
  set m := Multiset.card u.cycleType with hm
  have hsum : u.cycleType.sum = 2 * m := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hsign := sign_of_cycleType u
  rw [hs, hsum] at hsign
  have heven : Even (2 * m + m) := by
    have : ((-1 : ℤˣ)) ^ (2 * m + m) = 1 := hsign.symm
    exact (neg_one_pow_eq_one_iff_even (by decide)).mp this
  have hm0 : m ≠ 0 := by
    intro h0
    apply hu1
    rw [← cycleType_eq_zero]
    exact Multiset.card_eq_zero.mp h0
  have hm5 : 2 * m ≤ 11 := by
    rw [← hsum, sum_cycleType]
    have := Finset.card_le_univ u.support
    simpa using this
  have hfix : (fixF u).card = 11 - 2 * m := by
    have h1 := card_fixedPoints u
    rw [hsum] at h1
    have h2 : Fintype.card (Function.fixedPoints (⇑u)) = (fixF u).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun x => ⟨x.1, mem_fixF.mpr x.2⟩
          invFun := fun y => ⟨y.1, mem_fixF.mp y.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    rw [← h2, h1]
    simp
  obtain ⟨k, hk⟩ := heven
  rw [hfix]
  omega

theorem card_fixed_eq_seven {u σ : Perm (Fin 11)} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hs : sign u = 1) (hσ : orderOf σ = 5) (hc : u * σ = σ * u) : (fixF u).card = 7 := by
  have h37 := card_fixed_eq_three_or_seven hu2 hu1 hs
  have hf := card_fix_five hσ
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h3 := card_fix_modEq (g := u) (h := σ) hc (p := 5) (n := 1)
    (by rw [pow_one, ← hσ]; exact pow_orderOf_eq_one σ)
  have h4 := card_fix_modEq (g := σ) (h := u) hc.symm (p := 2) (n := 1) (by rw [pow_one]; exact hu2)
  have hinter : fixF σ ∩ fixF u = fixF u ∩ fixF σ := Finset.inter_comm _ _
  rw [hinter] at h4
  have hle1 : (fixF u ∩ fixF σ).card ≤ (fixF u).card := Finset.card_le_card Finset.inter_subset_left
  have hle2 : (fixF u ∩ fixF σ).card ≤ (fixF σ).card :=
    Finset.card_le_card Finset.inter_subset_right
  unfold Nat.ModEq at h3 h4
  omega

theorem card_le_four_of_commute_five {U : Subgroup (Perm (Fin 11))}
    (hUA : U ≤ alternatingGroup (Fin 11)) (hU2 : ∀ u ∈ U, u ^ 2 = 1) {σ : Perm (Fin 11)}
    (hσ : orderOf σ = 5) (hUσ : ∀ u ∈ U, u * σ = σ * u) : Nat.card U ≤ 4 := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group U (Fin 11)
  have hfix : ∀ g : U, Fintype.card (MulAction.fixedBy (Fin 11) g) =
      if g = 1 then 11 else 7 := by
    intro g
    split_ifs with hg
    · rw [hg]
      simp
    · have hu1 : (g : Perm (Fin 11)) ≠ 1 := fun h => hg (Subtype.ext h)
      have h7 := card_fixed_eq_seven (hU2 g g.2) hu1 (mem_alternatingGroup.mp (hUA g.2)) hσ
        (hUσ g g.2)
      rw [← h7, ← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun x => ⟨x.1, mem_fixF.mpr x.2⟩
          invFun := fun y => ⟨y.1, mem_fixF.mp y.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
  simp_rw [hfix] at hburn
  have hsum : ∑ g : U, (if g = 1 then 11 else 7) = 7 * Fintype.card U + 4 := by
    have : ∀ g : U, (if g = 1 then 11 else 7) = 7 + (if g = 1 then 4 else 0) := by
      intro g
      split_ifs <;> rfl
    simp_rw [this]
    rw [Finset.sum_add_distrib]
    simp
    ring
  rw [hsum] at hburn
  have hdvd : Fintype.card U ∣ 4 := by
    have : Fintype.card U ∣ 7 * Fintype.card U + 4 := ⟨_, by rw [hburn, mul_comm]⟩
    exact (Nat.dvd_add_right (Dvd.intro_left 7 rfl)).mp this
  rw [Nat.card_eq_fintype_card]
  exact Nat.le_of_dvd (by norm_num) hdvd

end CFSG.RankThree.PartOne.LyPerm
