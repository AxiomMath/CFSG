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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.InformationTheory.Hamming
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Classical.CosetLeaders

open scoped symmDiff

variable {C : Type*}

theorem sub_eq_add_zmod2 (x y : C → ZMod 2) : x - y = x + y :=
  funext fun i => CharTwo.sub_eq_add (x i) (y i)

theorem add_eq_zero_iff_eq_zmod2 {x y : C → ZMod 2} : x + y = 0 ↔ x = y := by
  rw [← sub_eq_add_zmod2, sub_eq_zero]

theorem card_symmDiff_add [DecidableEq C] (A B : Finset C) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have h₁ : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, Finset.sup_eq_union]
    exact Finset.card_union_of_disjoint disjoint_sdiff_sdiff
  have h₂ := Finset.card_sdiff_add_card_inter A B
  have h₃ := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at h₃
  omega

variable [Fintype C]

@[expose] def supp (x : C → ZMod 2) : Finset C := Finset.univ.filter fun i => x i ≠ 0

@[expose] def blocks (K : Submodule (ZMod 2) (C → ZMod 2)) : Set (Finset C) :=
  {B | ∃ x ∈ K, hammingNorm x = 6 ∧ supp x = B}

theorem mem_supp {x : C → ZMod 2} {i : C} : i ∈ supp x ↔ x i ≠ 0 := by simp [supp]

theorem hammingNorm_eq_card_supp (x : C → ZMod 2) : hammingNorm x = (supp x).card := rfl

private theorem zmod2_eq_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem supp_injective : Function.Injective (supp : (C → ZMod 2) → Finset C) := by
  intro x y h
  funext i
  have := congrArg (i ∈ ·) h
  simp only [mem_supp, eq_iff_iff] at this
  rcases zmod2_eq_zero_or_one (x i) with hx | hx <;>
    rcases zmod2_eq_zero_or_one (y i) with hy | hy <;> simp_all

variable [DecidableEq C]

theorem supp_add (x y : C → ZMod 2) : supp (x + y) = supp x ∆ supp y := by
  ext i
  simp only [mem_supp, Pi.add_apply, Finset.mem_symmDiff]
  have : ∀ a b : ZMod 2, a + b ≠ 0 ↔ (a ≠ 0 ∧ ¬b ≠ 0 ∨ b ≠ 0 ∧ ¬a ≠ 0) := by decide
  exact this (x i) (y i)

theorem hammingNorm_add_le (x y : C → ZMod 2) :
    hammingNorm (x + y) ≤ hammingNorm x + hammingNorm y := by
  rw [hammingNorm_eq_card_supp, hammingNorm_eq_card_supp, hammingNorm_eq_card_supp, supp_add]
  have := card_symmDiff_add (supp x) (supp y)
  omega

@[expose] def ind (T : Finset C) : C → ZMod 2 := fun i => if i ∈ T then 1 else 0

theorem supp_ind (T : Finset C) : supp (ind T) = T := by
  ext i
  by_cases h : i ∈ T <;> simp [mem_supp, ind, h]

theorem supp_single (i : C) : supp (Pi.single i (1 : ZMod 2)) = {i} := by
  ext j
  by_cases h : j = i
  · subst h
    simp [mem_supp]
  · simp [mem_supp, h]

theorem card_filter_hammingNorm (k : ℕ) :
    (Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = k).card =
      (Fintype.card C).choose k := by
  rw [← Finset.card_univ, ← Finset.card_powersetCard]
  refine Finset.card_nbij' supp ind ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard, Finset.subset_univ] at hx ⊢
    rw [← hammingNorm_eq_card_supp]
    exact hx
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard, Finset.subset_univ] at hT ⊢
    rw [hammingNorm_eq_card_supp, supp_ind]
    exact hT
  · intro x _
    exact supp_injective (supp_ind (supp x))
  · intro T _
    exact supp_ind T

theorem ncard_hammingNorm (k : ℕ) :
    {x : C → ZMod 2 | hammingNorm x = k}.ncard = (Fintype.card C).choose k := by
  rw [← card_filter_hammingNorm k, ← Set.ncard_coe_finset, Finset.coe_filter]
  simp

variable {K : Submodule (ZMod 2) (C → ZMod 2)}

omit [Fintype C] [DecidableEq C] in
theorem mkQ_eq_iff {x y : C → ZMod 2} : K.mkQ x = K.mkQ y ↔ x + y ∈ K := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, sub_eq_add_zmod2]

theorem eq_of_mkQ_eq (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x) {x y : C → ZMod 2}
    (hx : hammingNorm x ≤ 2) (hy : hammingNorm y ≤ 2) (h : K.mkQ x = K.mkQ y) : x = y := by
  rw [mkQ_eq_iff] at h
  by_contra hne
  have h₁ := hmin _ h (fun h0 => hne (add_eq_zero_iff_eq_zmod2.1 h0))
  have h₂ := hammingNorm_add_le x y
  omega

theorem mkQ_ne_of_three (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x) {x y : C → ZMod 2}
    (hx : hammingNorm x = 3) (hy : hammingNorm y ≤ 2) : K.mkQ x ≠ K.mkQ y := by
  intro h
  rw [mkQ_eq_iff] at h
  have hne : x + y ≠ 0 := fun h0 => by
    rw [add_eq_zero_iff_eq_zmod2] at h0
    subst h0
    omega
  have h₁ := hmin _ h hne
  have h₂ := hammingNorm_add_le x y
  omega

theorem mkQ_eq_iff_block (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x) {x y : C → ZMod 2}
    (hx : hammingNorm x = 3) (hy : hammingNorm y = 3) (hne : x ≠ y) :
    K.mkQ x = K.mkQ y ↔ Disjoint (supp x) (supp y) ∧ supp x ∪ supp y ∈ blocks K := by
  rw [mkQ_eq_iff]
  constructor
  · intro h
    have h₁ := hmin _ h (fun h0 => hne (add_eq_zero_iff_eq_zmod2.1 h0))
    have h₂ := card_symmDiff_add (supp x) (supp y)
    rw [hammingNorm_eq_card_supp, supp_add] at h₁
    rw [← hammingNorm_eq_card_supp, ← hammingNorm_eq_card_supp, hx, hy] at h₂
    have hinter : (supp x ∩ supp y).card = 0 := by omega
    have hdisj : Disjoint (supp x) (supp y) :=
      Finset.disjoint_iff_inter_eq_empty.2 (Finset.card_eq_zero.1 hinter)
    refine ⟨hdisj, x + y, h, ?_, ?_⟩
    · rw [hammingNorm_eq_card_supp, supp_add]
      omega
    · rw [supp_add, hdisj.symmDiff_eq_sup, Finset.sup_eq_union]
  · rintro ⟨hdisj, z, hz, -, hzB⟩
    have : x + y = z := by
      apply supp_injective
      rw [supp_add, hdisj.symmDiff_eq_sup, Finset.sup_eq_union, hzB]
    rw [this]
    exact hz

theorem existsUnique_partner (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x)
    (hS : ∀ T : Finset C, T.card = 3 → ∃! B, B ∈ blocks K ∧ T ⊆ B) {x : C → ZMod 2}
    (hx : hammingNorm x = 3) :
    ∃! y : C → ZMod 2, hammingNorm y = 3 ∧ y ≠ x ∧ K.mkQ y = K.mkQ x := by
  obtain ⟨B, ⟨⟨z, hz, hz6, hzB⟩, hTB⟩, huniq⟩ := hS (supp x) hx
  have hsy : supp (z + x) = B \ supp x := by
    rw [supp_add, hzB, symmDiff_of_ge hTB]
  have hB6 : B.card = 6 := by rw [← hzB, ← hammingNorm_eq_card_supp, hz6]
  have hy3 : hammingNorm (z + x) = 3 := by
    rw [hammingNorm_eq_card_supp, hsy, Finset.card_sdiff_of_subset hTB, hB6,
      ← hammingNorm_eq_card_supp, hx]
  refine ⟨z + x, ⟨hy3, fun h => ?_, ?_⟩, ?_⟩
  · have hz0 : z = 0 := by
      have := congrArg (· + x) h
      simpa only [add_assoc, ← sub_eq_add_zmod2 x x, sub_self, add_zero] using this
    rw [hz0, hammingNorm_zero] at hz6
    omega
  · rw [mkQ_eq_iff, add_assoc, ← sub_eq_add_zmod2 x x, sub_self, add_zero]
    exact hz
  · rintro y ⟨hy, hyx, hyK⟩
    obtain ⟨hdisj, hblk⟩ := (mkQ_eq_iff_block hmin hy hx hyx).1 hyK
    have hB' : supp y ∪ supp x = B := huniq _ ⟨hblk, Finset.subset_union_right⟩
    apply supp_injective
    rw [hsy, ← hB', Finset.union_sdiff_right, hdisj.sdiff_eq_left]

theorem ncard_fiber (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x)
    (hS : ∀ T : Finset C, T.card = 3 → ∃! B, B ∈ blocks K ∧ T ⊆ B) {x : C → ZMod 2}
    (hx : hammingNorm x = 3) :
    {y : C → ZMod 2 | hammingNorm y = 3 ∧ K.mkQ y = K.mkQ x}.ncard = 2 := by
  obtain ⟨x', ⟨hx', hne, hK'⟩, huniq⟩ := existsUnique_partner hmin hS hx
  have h : {y : C → ZMod 2 | hammingNorm y = 3 ∧ K.mkQ y = K.mkQ x} = {x, x'} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hyK⟩
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr (huniq y ⟨hy, hyx, hyK⟩)
    · rintro (rfl | rfl)
      · exact ⟨hx, rfl⟩
      · exact ⟨hx', hK'⟩
  rw [h, Set.ncard_pair hne.symm]

theorem card_filter_le_two (hC : Fintype.card C = 22) :
    (Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x ≤ 2).card = 254 := by
  rw [Finset.card_eq_sum_card_image hammingNorm]
  have himg : (Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x ≤ 2).image hammingNorm ⊆
      Finset.range 3 := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_range]
    omega
  rw [Finset.sum_subset himg ?_]
  · have hk : ∀ k ∈ Finset.range 3,
        ({a ∈ Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x ≤ 2 |
          hammingNorm a = k}).card = (Fintype.card C).choose k := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.filter_filter, ← card_filter_hammingNorm k]
      congr 1
      exact Finset.filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    rw [Finset.sum_congr rfl hk, hC]
    decide
  · intro k hk hk'
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hxk
    exact hk' (Finset.mem_image.2 ⟨x, hx, hxk⟩)

omit [DecidableEq C] in
theorem card_quotient (hC : Fintype.card C = 22) (hK : Module.finrank (ZMod 2) K = 12) :
    Nat.card ((C → ZMod 2) ⧸ K) = 1024 := by
  have h := Submodule.finrank_quotient_add_finrank K
  rw [Module.finrank_fintype_fun_eq_card, hC, hK] at h
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    show Module.finrank (ZMod 2) ((C → ZMod 2) ⧸ K) = 10 by omega]
  norm_num

theorem ncard_image_three (hC : Fintype.card C = 22) (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x)
    (hS : ∀ T : Finset C, T.card = 3 → ∃! B, B ∈ blocks K ∧ T ⊆ B) :
    (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = 3}).ncard = 770 := by
  classical
  have hF : (Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3).card = 1540 := by
    rw [card_filter_hammingNorm, hC]
    decide
  have hfib : ∀ b ∈ (Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3).image K.mkQ,
      ({a ∈ Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3 | K.mkQ a = b}).card =
        2 := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    calc ({a ∈ Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3 |
          K.mkQ a = K.mkQ x}).card =
        {y : C → ZMod 2 | hammingNorm y = 3 ∧ K.mkQ y = K.mkQ x}.ncard := by
          rw [← Set.ncard_coe_finset]
          congr 1
          ext y
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq]
      _ = 2 := ncard_fiber hmin hS hx
  have hsum := Finset.card_eq_sum_card_image K.mkQ
    (Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3)
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hF] at hsum
  have himg :
      ((Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3).image K.mkQ).card = 770 := by
    omega
  rw [← himg, ← Set.ncard_coe_finset, Finset.coe_image, Finset.coe_filter]
  simp

omit [DecidableEq C] in
theorem setOf_hammingNorm_zero : {x : C → ZMod 2 | hammingNorm x = 0} = {0} := by
  ext x
  simp

theorem setOf_hammingNorm_one :
    {x : C → ZMod 2 | hammingNorm x = 1} = Set.range fun i => Pi.single i 1 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hx
    rw [hammingNorm_eq_card_supp, Finset.card_eq_one] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, supp_injective (by rw [supp_single, hi])⟩
  · rintro ⟨i, rfl⟩
    rw [hammingNorm_eq_card_supp, supp_single, Finset.card_singleton]

theorem ncard_image_le_two (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x) {k : ℕ} (hk : k ≤ 2) :
    (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = k}).ncard = (Fintype.card C).choose k := by
  rw [Set.InjOn.ncard_image, ncard_hammingNorm]
  intro x hx y hy h
  simp only [Set.mem_ofPred_eq] at hx hy
  exact eq_of_mkQ_eq hmin (by omega) (by omega) h

theorem exists_rep (hC : Fintype.card C = 22) (hK : Module.finrank (ZMod 2) K = 12)
    (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x)
    (hS : ∀ T : Finset C, T.card = 3 → ∃! B, B ∈ blocks K ∧ T ⊆ B) (c : (C → ZMod 2) ⧸ K) :
    ∃ x : C → ZMod 2, hammingNorm x ≤ 3 ∧ K.mkQ x = c := by
  classical
  have hA : ((Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x ≤ 2).image K.mkQ).card =
      254 := by
    rw [Finset.card_image_of_injOn, card_filter_le_two hC]
    intro x hx y hy h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
    exact eq_of_mkQ_eq hmin hx hy h
  have hB : ((Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3).image K.mkQ).card =
      770 := by
    rw [← ncard_image_three hC hmin hS, ← Set.ncard_coe_finset, Finset.coe_image,
      Finset.coe_filter]
    simp
  have hdisj : Disjoint ((Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x ≤ 2).image K.mkQ)
      ((Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3).image K.mkQ) := by
    rw [Finset.disjoint_left]
    intro b hb₂ hb₃
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb₂
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 hb₃
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact mkQ_ne_of_three hmin hy hx hxy
  have hcard : ((Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x ≤ 2).image K.mkQ ∪
      (Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3).image K.mkQ).card =
        Fintype.card ((C → ZMod 2) ⧸ K) := by
    rw [Finset.card_union_of_disjoint hdisj, hA, hB, Fintype.card_eq_nat_card,
      card_quotient hC hK]
  have hc : c ∈ (Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x ≤ 2).image K.mkQ ∪
      (Finset.univ.filter fun x : C → ZMod 2 => hammingNorm x = 3).image K.mkQ := by
    rw [Finset.eq_univ_of_card _ hcard]
    exact Finset.mem_univ c
  rcases Finset.mem_union.1 hc with h | h
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨x, by omega, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨x, by omega, rfl⟩

theorem pairwise_disjoint_image (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x) :
    Pairwise fun j k : Fin 4 => Disjoint (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = j})
      (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = k}) := by
  intro j k hjk
  have hjk' : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
  have hj := j.2
  have hk := k.2
  rw [Set.disjoint_left]
  rintro b ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  simp only [Set.mem_ofPred_eq] at hx hy
  by_cases hj3 : (j : ℕ) = 3
  · exact mkQ_ne_of_three hmin (hx.trans hj3) (by omega) hxy.symm
  · by_cases hk3 : (k : ℕ) = 3
    · exact mkQ_ne_of_three hmin (hy.trans hk3) (by omega) hxy
    · have := eq_of_mkQ_eq hmin (x := y) (y := x) (by omega) (by omega) hxy
      subst this
      exact hjk' (hx.symm.trans hy)

theorem iUnion_image (hC : Fintype.card C = 22) (hK : Module.finrank (ZMod 2) K = 12)
    (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x)
    (hS : ∀ T : Finset C, T.card = 3 → ∃! B, B ∈ blocks K ∧ T ⊆ B) :
    (⋃ k : Fin 4, K.mkQ '' {x : C → ZMod 2 | hammingNorm x = k}) = Set.univ := by
  refine Set.eq_univ_of_forall fun c => ?_
  obtain ⟨x, hx, rfl⟩ := exists_rep hC hK hmin hS c
  exact Set.mem_iUnion.2 ⟨⟨hammingNorm x, by omega⟩, x, rfl, rfl⟩

theorem binary_steiner_code_coset_leaders (hC : Fintype.card C = 22)
    (K : Submodule (ZMod 2) (C → ZMod 2)) (hK : Module.finrank (ZMod 2) K = 12)
    (hmin : ∀ x ∈ K, x ≠ 0 → 6 ≤ hammingNorm x)
    (hS : ∀ T : Finset C, T.card = 3 → ∃! B, B ∈ blocks K ∧ T ⊆ B) :
    (∀ c : (C → ZMod 2) ⧸ K, ∃ x : C → ZMod 2, hammingNorm x ≤ 3 ∧ K.mkQ x = c) ∧
    (∀ x y : C → ZMod 2, hammingNorm x ≤ 2 → hammingNorm y ≤ 2 → K.mkQ x = K.mkQ y → x = y) ∧
    (∀ x y : C → ZMod 2, hammingNorm x = 3 → hammingNorm y ≤ 2 → K.mkQ x ≠ K.mkQ y) ∧
    (∀ x y : C → ZMod 2, hammingNorm x = 3 → hammingNorm y = 3 → x ≠ y →
      (K.mkQ x = K.mkQ y ↔ Disjoint (supp x) (supp y) ∧ supp x ∪ supp y ∈ blocks K)) ∧
    (∀ x : C → ZMod 2, hammingNorm x = 3 →
      ∃! y : C → ZMod 2, hammingNorm y = 3 ∧ y ≠ x ∧ K.mkQ y = K.mkQ x) ∧
    (∀ x : C → ZMod 2, hammingNorm x = 3 →
      {y : C → ZMod 2 | hammingNorm y = 3 ∧ K.mkQ y = K.mkQ x}.ncard = 2) ∧
    {x : C → ZMod 2 | hammingNorm x = 0} = {0} ∧
    {x : C → ZMod 2 | hammingNorm x = 1} = Set.range (fun i => Pi.single i 1) ∧
    {x : C → ZMod 2 | hammingNorm x = 1}.ncard = 22 ∧
    {x : C → ZMod 2 | hammingNorm x = 2}.ncard = 231 ∧
    {x : C → ZMod 2 | hammingNorm x = 3}.ncard = 1540 ∧
    (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = 0}).ncard = 1 ∧
    (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = 1}).ncard = 22 ∧
    (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = 2}).ncard = 231 ∧
    (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = 3}).ncard = 770 ∧
    Pairwise (fun j k : Fin 4 => Disjoint (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = j})
      (K.mkQ '' {x : C → ZMod 2 | hammingNorm x = k})) ∧
    (⋃ k : Fin 4, K.mkQ '' {x : C → ZMod 2 | hammingNorm x = k}) = Set.univ ∧
    1 + 22 + 231 + 770 = 1024 ∧ Nat.card ((C → ZMod 2) ⧸ K) = 1024 := by
  refine ⟨exists_rep hC hK hmin hS, fun x y hx hy => eq_of_mkQ_eq hmin hx hy,
    fun x y hx hy => mkQ_ne_of_three hmin hx hy, fun x y hx hy => mkQ_eq_iff_block hmin hx hy,
    fun x hx => existsUnique_partner hmin hS hx, fun x hx => ncard_fiber hmin hS hx,
    setOf_hammingNorm_zero, setOf_hammingNorm_one, ?_, ?_, ?_, ?_, ?_, ?_,
    ncard_image_three hC hmin hS, pairwise_disjoint_image hmin, iUnion_image hC hK hmin hS,
    by norm_num, card_quotient hC hK⟩
  · rw [ncard_hammingNorm, hC]
    rfl
  · rw [ncard_hammingNorm, hC]
    rfl
  · rw [ncard_hammingNorm, hC]
    rfl
  · rw [ncard_image_le_two hmin (by norm_num), hC]
    rfl
  · rw [ncard_image_le_two hmin (by norm_num), hC]
    rfl
  · rw [ncard_image_le_two hmin (by norm_num), hC]
    rfl

end CFSG.Monster.B.Classical.CosetLeaders
