module

public import CFSG.GroupActions.PrimitiveNormal
public import CFSG.GroupActions.PrimitiveNormalTransitive
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Monster.B.Generic

open Subgroup MulAction

private theorem sign_eq_neg_one_of_sq_eq_one_of_forall_ne {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Equiv.Perm α} {m : ℕ} (hcard : Fintype.card α = 2 * m) (hm : Odd m) (h2 : σ ^ 2 = 1)
    (hfix : ∀ y, σ y ≠ y) : Equiv.Perm.sign σ = -1 := by
  have hpos : 0 < Fintype.card α := by rw [hcard]; exact Nat.mul_pos two_pos hm.pos
  obtain ⟨y⟩ := Fintype.card_pos_iff.mp hpos
  have hσ1 : σ ≠ 1 := fun h => hfix y (by rw [h, Equiv.Perm.one_apply])
  have hord : orderOf σ = 2 := orderOf_eq_prime h2 hσ1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  have hsupp : σ.support = Finset.univ :=
    Finset.eq_univ_of_forall fun z => Equiv.Perm.mem_support.mpr (hfix z)
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hn, hsupp, Finset.card_univ, hcard, Multiset.sum_replicate, smul_eq_mul, hord] at hsum
  rw [Equiv.Perm.sign_of_cycleType, hn, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul, hord]
  have hnm : n + 1 = m := by omega
  rw [hnm]
  obtain ⟨k, rfl⟩ := hm
  exact Odd.neg_one_pow ⟨3 * k + 1, by ring⟩

private theorem mem_zpowers_iff_of_orderOf_eq_two {G : Type*} [Group G] {a y : G}
    (ha : orderOf a = 2) : y ∈ zpowers a ↔ y = 1 ∨ y = a := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rcases Int.even_or_odd k with hk | ⟨j, rfl⟩
    · left
      exact orderOf_dvd_iff_zpow_eq_one.mp
        (by rw [ha, Nat.cast_ofNat]; exact even_iff_two_dvd.mp hk)
    · right
      rw [zpow_add_one, orderOf_dvd_iff_zpow_eq_one.mp
        (by rw [ha, Nat.cast_ofNat]; exact dvd_mul_right 2 j), one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

variable {K Ω : Type*} [Group K] [MulAction K Ω]

private theorem bijective_smul_of_inf_eq_bot {N : Subgroup K} [IsPretransitive N Ω] {x : Ω}
    (hNx : N ⊓ stabilizer K x = ⊥) : Function.Bijective (fun n : N => n • x) := by
  refine ⟨fun n₁ n₂ h => ?_, fun y => exists_smul_eq N x y⟩
  have h' : (n₁ : K) • x = (n₂ : K) • x := h
  have hmem : (n₁ : K)⁻¹ * n₂ ∈ N ⊓ stabilizer K x := by
    refine mem_inf.mpr ⟨N.mul_mem (N.inv_mem n₁.2) n₂.2, ?_⟩
    rw [mem_stabilizer_iff, mul_smul, ← h', inv_smul_smul]
  rw [hNx, mem_bot, inv_mul_eq_one] at hmem
  exact Subtype.ext hmem

private theorem false_of_inf_stabilizer_eq_bot [Finite K] [FaithfulSMul K Ω] [IsPreprimitive K Ω]
    {m : ℕ} (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m) {x : Ω} {N : Subgroup K}
    (hN : N.Normal) (hNbot : N ≠ ⊥) (hNx : N ⊓ stabilizer K x = ⊥) : False := by
  classical
  have : Nonempty Ω := ⟨x⟩
  have : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  let : Fintype Ω := Fintype.ofFinite Ω
  have := hN
  have := CFSG.GroupActions.isPretransitive_of_normal_ne_bot (Ω := Ω) N hNbot
  have hbij := bijective_smul_of_inf_eq_bot (N := N) hNx
  have hcardN : Nat.card N = 2 * m := (Nat.card_congr (Equiv.ofBijective _ hbij)).trans hΩ
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := N) 2
    (by rw [hcardN]; exact dvd_mul_right 2 m)
  have ht2 : (t : K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
  have hst : Equiv.Perm.sign (MulAction.toPermHom K Ω (t : K)) = -1 := by
    refine sign_eq_neg_one_of_sq_eq_one_of_forall_ne (m := m) ?_ hmodd ?_ ?_
    · rw [← Nat.card_eq_fintype_card, hΩ]
    · rw [← map_pow, ht2, map_one]
    · intro y hy
      obtain ⟨n, rfl⟩ := hbij.2 y
      have h1 : (t * n) • x = n • x := by rw [mul_smul]; exact hy
      have h2 : t * n = n := hbij.1 h1
      rw [mul_eq_right] at h2
      rw [h2, orderOf_one] at ht
      omega
  have hMbot : N ⊓ (Equiv.Perm.sign.comp (MulAction.toPermHom K Ω)).ker ≠ ⊥ := by
    intro hM
    have hinj : Function.Injective
        ((Equiv.Perm.sign.comp (MulAction.toPermHom K Ω)).comp N.subtype) := by
      rw [injective_iff_map_eq_one]
      intro n hn
      have hmem : (n : K) ∈ N ⊓ (Equiv.Perm.sign.comp (MulAction.toPermHom K Ω)).ker :=
        ⟨n.2, MonoidHom.mem_ker.mpr hn⟩
      rw [hM, mem_bot] at hmem
      exact Subtype.ext hmem
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcardN, Nat.card_eq_fintype_card, Fintype.card_units_int] at hle
    omega
  have := CFSG.GroupActions.isPretransitive_of_normal_ne_bot (Ω := Ω) _ hMbot
  obtain ⟨u, hu⟩ := exists_smul_eq
    (N ⊓ (Equiv.Perm.sign.comp (MulAction.toPermHom K Ω)).ker : Subgroup K) x ((t : K) • x)
  have htu : (⟨u, u.2.1⟩ : N) = t := hbij.1 hu
  have h1 : Equiv.Perm.sign (MulAction.toPermHom K Ω (t : K)) = 1 := by
    rw [← htu]
    exact MonoidHom.mem_ker.mp u.2.2
  rw [hst] at h1
  exact absurd h1 (by decide)

private theorem false_of_commute [Finite K] [FaithfulSMul K Ω] [IsPreprimitive K Ω] {m : ℕ}
    (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m) (x : Ω) {N : Subgroup K}
    (hN : N.Normal) (hNbot : N ≠ ⊥) (hcomm : ∀ g ∈ N, ∀ h ∈ N, g * h = h * g) : False := by
  have : Nonempty Ω := ⟨x⟩
  have := hN
  have := CFSG.GroupActions.isPretransitive_of_normal_ne_bot (Ω := Ω) N hNbot
  refine false_of_inf_stabilizer_eq_bot hΩ hm1 hmodd (x := x) hN hNbot ?_
  rw [eq_bot_iff]
  rintro g ⟨hgN, hgx⟩
  rw [mem_bot]
  refine eq_of_smul_eq_smul (α := Ω) fun y => ?_
  obtain ⟨n, rfl⟩ := exists_smul_eq N x y
  rw [one_smul, Subgroup.smul_def, ← mul_smul, hcomm g hgN n n.2, mul_smul,
    mem_stabilizer_iff.mp hgx]

private theorem notMem_of_ne_top {a : K} (hgen : normalClosure {a} = ⊤) {N : Subgroup K}
    (hN : N.Normal) (hNtop : N ≠ ⊤) : a ∉ N := by
  intro haN
  have := hN
  apply hNtop
  rw [eq_top_iff, ← hgen]
  exact normalClosure_le_normal (Set.singleton_subset_iff.mpr haN)

private theorem eq_top_of_commutator_le {a : K} (hgen : normalClosure {a} = ⊤) {S : Subgroup K}
    (hS : commutator K ≤ S) (haS : a ∈ S) : S = ⊤ := by
  have := Subgroup.Normal.of_commutator_le (h := hS)
  rw [eq_top_iff, ← hgen]
  exact normalClosure_le_normal (Set.singleton_subset_iff.mpr haS)

private theorem exists_mem_inf_stabilizer [Finite K] [FaithfulSMul K Ω] [IsPreprimitive K Ω]
    {m : ℕ} (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m) {x : Ω} {a : K}
    (hax : a ∈ stabilizer K x) (ha2 : orderOf a = 2)
    [(zpowers (⟨a, hax⟩ : stabilizer K x)).Normal]
    (hsimple : IsSimpleGroup (stabilizer K x ⧸ zpowers (⟨a, hax⟩ : stabilizer K x)))
    {N : Subgroup K} (hN : N.Normal) (hNbot : N ≠ ⊥) (haN : a ∉ N) :
    ∀ h ∈ stabilizer K x, ∃ u ∈ N ⊓ stabilizer K x, h = u ∨ h = u * a := by
  have ha2' : orderOf (⟨a, hax⟩ : stabilizer K x) = 2 := by rw [Subgroup.orderOf_mk, ha2]
  have := hsimple
  have : ((N.subgroupOf (stabilizer K x)).map
      (QuotientGroup.mk' (zpowers (⟨a, hax⟩ : stabilizer K x)))).Normal :=
    (hN.subgroupOf _).map _ (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((N.subgroupOf (stabilizer K x)).map
      (QuotientGroup.mk' (zpowers (⟨a, hax⟩ : stabilizer K x)))) with hbot | htop
  · refine (false_of_inf_stabilizer_eq_bot hΩ hm1 hmodd (x := x) hN hNbot ?_).elim
    rw [eq_bot_iff]
    rintro u ⟨huN, huH⟩
    have hmem := mem_map_of_mem (QuotientGroup.mk' (zpowers (⟨a, hax⟩ : stabilizer K x)))
      (mem_subgroupOf.mpr huN : (⟨u, huH⟩ : stabilizer K x) ∈ N.subgroupOf (stabilizer K x))
    rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    rcases (mem_zpowers_iff_of_orderOf_eq_two ha2').mp hmem with h1 | h1
    · exact mem_bot.mpr (congrArg Subtype.val h1)
    · have hua : u = a := congrArg Subtype.val h1
      exact absurd (hua ▸ huN) haN
  · intro h hh
    have hmem : QuotientGroup.mk' (zpowers (⟨a, hax⟩ : stabilizer K x)) ⟨h, hh⟩ ∈
        (N.subgroupOf (stabilizer K x)).map
          (QuotientGroup.mk' (zpowers (⟨a, hax⟩ : stabilizer K x))) := by
      rw [htop]; exact mem_top _
    obtain ⟨u, hu, hπ⟩ := mem_map.mp hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hπ
    have hq := QuotientGroup.eq.mp hπ
    refine ⟨u, ⟨mem_subgroupOf.mp hu, u.2⟩, ?_⟩
    rcases (mem_zpowers_iff_of_orderOf_eq_two ha2').mp hq with h1 | h1
    · left
      have h1' : (u : K)⁻¹ * h = 1 := congrArg Subtype.val h1
      exact (inv_mul_eq_one.mp h1').symm
    · right
      have h1' : (u : K)⁻¹ * h = a := congrArg Subtype.val h1
      exact inv_mul_eq_iff_eq_mul.mp h1'

private theorem index_eq_two_of_normal [Finite K] [FaithfulSMul K Ω] [IsPreprimitive K Ω]
    {m : ℕ} (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m) {x : Ω} {a : K}
    (hax : a ∈ stabilizer K x) (ha2 : orderOf a = 2) (hgen : normalClosure {a} = ⊤)
    [(zpowers (⟨a, hax⟩ : stabilizer K x)).Normal]
    (hsimple : IsSimpleGroup (stabilizer K x ⧸ zpowers (⟨a, hax⟩ : stabilizer K x)))
    {N : Subgroup K} (hN : N.Normal) (hNbot : N ≠ ⊥) (hNtop : N ≠ ⊤) : N.index = 2 := by
  have haN := notMem_of_ne_top hgen hN hNtop
  have hC := exists_mem_inf_stabilizer hΩ hm1 hmodd hax ha2 hsimple hN hNbot haN
  have : Nonempty Ω := ⟨x⟩
  have := hN
  have := CFSG.GroupActions.isPretransitive_of_normal_ne_bot (Ω := Ω) N hNbot
  have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
  rw [index_eq_two_iff_exists_notMem_and]
  refine ⟨a, haN, fun b => ?_⟩
  obtain ⟨n, hn, h, hh, rfl⟩ := CFSG.GroupActions.exists_mul_of_isPretransitive N x b
  obtain ⟨u, ⟨huN, -⟩, rfl | rfl⟩ := hC h hh
  · exact Or.inr (N.mul_mem hn huN)
  · left
    rw [mul_assoc, mul_assoc, haa, mul_one]
    exact N.mul_mem hn huN

private theorem complement_of_normal [Finite K] [FaithfulSMul K Ω] [IsPreprimitive K Ω]
    {m : ℕ} (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m) {x : Ω} {a : K}
    (hax : a ∈ stabilizer K x) (ha2 : orderOf a = 2) (hgen : normalClosure {a} = ⊤)
    [(zpowers (⟨a, hax⟩ : stabilizer K x)).Normal]
    (hsimple : IsSimpleGroup (stabilizer K x ⧸ zpowers (⟨a, hax⟩ : stabilizer K x)))
    {N : Subgroup K} (hN : N.Normal) (hNbot : N ≠ ⊥) (hNtop : N ≠ ⊤) :
    a ∉ N ∧ zpowers a ⊓ (N ⊓ stabilizer K x) = ⊥ ∧
      zpowers a ⊔ (N ⊓ stabilizer K x) = stabilizer K x ∧
      Function.Bijective (fun g : ↥(N ⊓ stabilizer K x) =>
        (QuotientGroup.mk (⟨g, g.2.2⟩ : stabilizer K x) :
          stabilizer K x ⧸ zpowers (⟨a, hax⟩ : stabilizer K x))) := by
  have haN := notMem_of_ne_top hgen hN hNtop
  have hC := exists_mem_inf_stabilizer hΩ hm1 hmodd hax ha2 hsimple hN hNbot haN
  have ha2' : orderOf (⟨a, hax⟩ : stabilizer K x) = 2 := by rw [Subgroup.orderOf_mk, ha2]
  refine ⟨haN, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro y ⟨hya, hyN, -⟩
    rcases (mem_zpowers_iff_of_orderOf_eq_two ha2).mp hya with rfl | rfl
    · exact one_mem _
    · exact absurd hyN haN
  · refine le_antisymm (sup_le (zpowers_le.mpr hax) inf_le_right) fun h hh => ?_
    obtain ⟨u, hu, rfl | rfl⟩ := hC h hh
    · exact mem_sup_right hu
    · exact mul_mem (mem_sup_right hu) (mem_sup_left (mem_zpowers a))
  · intro g₁ g₂ hg
    have hq := QuotientGroup.eq.mp hg
    rcases (mem_zpowers_iff_of_orderOf_eq_two ha2').mp hq with h1 | h1
    · have h1' : (g₁ : K)⁻¹ * g₂ = 1 := congrArg Subtype.val h1
      exact Subtype.ext (inv_mul_eq_one.mp h1')
    · have h1' : (g₁ : K)⁻¹ * g₂ = a := congrArg Subtype.val h1
      exact absurd (h1' ▸ N.mul_mem (N.inv_mem g₁.2.1) g₂.2.1) haN
  · intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu, rfl | rfl⟩ := hC h hh
    · exact ⟨⟨_, hu⟩, rfl⟩
    · refine ⟨⟨u, hu⟩, QuotientGroup.eq.mpr ?_⟩
      convert mem_zpowers (⟨a, hax⟩ : stabilizer K x) using 1
      ext
      simp

private theorem commutator_le_of_normal [Finite K] [FaithfulSMul K Ω] [IsPreprimitive K Ω]
    {m : ℕ} (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m) {x : Ω} {a : K}
    (hax : a ∈ stabilizer K x) (ha2 : orderOf a = 2) (hgen : normalClosure {a} = ⊤)
    [(zpowers (⟨a, hax⟩ : stabilizer K x)).Normal]
    (hsimple : IsSimpleGroup (stabilizer K x ⧸ zpowers (⟨a, hax⟩ : stabilizer K x)))
    {N : Subgroup K} (hN : N.Normal) (hNbot : N ≠ ⊥) : commutator K ≤ N := by
  by_cases hNtop : N = ⊤
  · rw [hNtop]; exact le_top
  have h2 := index_eq_two_of_normal hΩ hm1 hmodd hax ha2 hgen hsimple hN hNbot hNtop
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g _ h _
  rw [commutatorElement_def]
  simp only [mul_mem_iff_of_index_two h2, inv_mem_iff]
  tauto

private theorem commutator_ne_bot [Finite K] [FaithfulSMul K Ω] [IsPreprimitive K Ω] {m : ℕ}
    (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m) (x : Ω) {a : K}
    (ha2 : orderOf a = 2) : commutator K ≠ ⊥ := by
  intro h
  rw [commutator_eq_bot_iff] at h
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha2
    omega
  have : Nontrivial K := ⟨⟨a, 1, ha1⟩⟩
  exact false_of_commute hΩ hm1 hmodd x (N := ⊤) inferInstance
    (top_ne_bot : (⊤ : Subgroup K) ≠ ⊥) (fun g _ k _ => mul_comm' g k)

private theorem not_isMulCommutative_commutator [Finite K] [FaithfulSMul K Ω]
    [IsPreprimitive K Ω] {m : ℕ} (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m)
    (x : Ω) {a : K} (ha2 : orderOf a = 2) : ¬ IsMulCommutative (commutator K) := by
  intro hcomm
  refine false_of_commute hΩ hm1 hmodd x (N := commutator K) inferInstance
    (commutator_ne_bot hΩ hm1 hmodd x ha2) ?_
  intro g hg h hh
  exact congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : commutator K) ⟨h, hh⟩)

private theorem normal_map_subtype_of_conjNormal_mem {a : K} (hgen : normalClosure {a} = ⊤)
    (ha2 : orderOf a = 2) (T : Subgroup (commutator K)) [T.Normal]
    (hT : ∀ t ∈ T, MulAut.conjNormal a t ∈ T) : (T.map (commutator K).subtype).Normal := by
  have hainv : a⁻¹ = a := inv_eq_self_of_orderOf_eq_two ha2
  have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
  rw [← normalizer_eq_top_iff]
  refine eq_top_of_commutator_le hgen ?_ ?_
  · have := le_normalizer_map (H := T) (commutator K).subtype
    rwa [normalizer_eq_top T, ← MonoidHom.range_eq_map, range_subtype] at this
  · rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, hT t ht, rfl⟩
    · rintro ⟨t, ht, hth⟩
      refine ⟨_, hT t ht, ?_⟩
      have hth' : (t : K) = a * h * a⁻¹ := hth
      show a * (t : K) * a⁻¹ = h
      rw [hth', hainv]
      calc a * (a * h * a) * a = (a * a) * h * (a * a) := by simp only [mul_assoc]
        _ = h := by rw [haa, one_mul, mul_one]

private theorem isSimpleGroup_commutator [Finite K] [FaithfulSMul K Ω] [IsPreprimitive K Ω]
    {m : ℕ} (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m) {x : Ω} {a : K}
    (hax : a ∈ stabilizer K x) (ha2 : orderOf a = 2) (hgen : normalClosure {a} = ⊤)
    [(zpowers (⟨a, hax⟩ : stabilizer K x)).Normal]
    (hsimple : IsSimpleGroup (stabilizer K x ⧸ zpowers (⟨a, hax⟩ : stabilizer K x)))
    (hsq : ∀ s : ℕ, Nat.card K ≠ 2 * s ^ 2) : IsSimpleGroup (commutator K) := by
  have hDbot := commutator_ne_bot hΩ hm1 hmodd x ha2
  have hainv : a⁻¹ = a := inv_eq_self_of_orderOf_eq_two ha2
  have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
  have key : ∀ T : Subgroup (commutator K), T.Normal →
      (∀ t ∈ T, MulAut.conjNormal a t ∈ T) → T ≠ ⊥ → T = ⊤ := by
    intro T hT hTc hTbot
    have hnorm := normal_map_subtype_of_conjNormal_mem hgen ha2 T hTc
    have hne : T.map (commutator K).subtype ≠ ⊥ := by
      rwa [Ne, map_eq_bot_iff_of_injective T (commutator K).subtype_injective]
    have hle := commutator_le_of_normal hΩ hm1 hmodd hax ha2 hgen hsimple hnorm hne
    rw [eq_top_iff]
    rintro d -
    obtain ⟨t, ht, htd⟩ := hle d.2
    rwa [show t = d from Subtype.ext htd] at ht
  rw [isSimpleGroup_iff]
  refine ⟨(nontrivial_iff_ne_bot _).mpr hDbot, ?_⟩
  intro E hE
  by_cases hEbot : E = ⊥
  · exact Or.inl hEbot
  right
  set c : MulAut (commutator K) := MulAut.conjNormal a with hc
  have hcc : ∀ d, c (c d) = d := by
    intro d
    apply Subtype.ext
    simp only [hc, MulAut.conjNormal_apply, hainv]
    calc a * (a * ↑d * a) * a = (a * a) * ↑d * (a * a) := by simp only [mul_assoc]
      _ = ↑d := by rw [haa, one_mul, mul_one]
  set F : Subgroup (commutator K) := E.comap c.toMonoidHom
  have : F.Normal := hE.comap _
  have hEF_c : ∀ t ∈ E ⊓ F, c t ∈ E ⊓ F := fun t ht =>
    ⟨ht.2, show c (c t) ∈ E by rw [hcc]; exact ht.1⟩
  by_cases hEF : E ⊓ F = ⊥
  · exfalso
    have hsup : E ⊔ F = ⊤ := by
      refine key (E ⊔ F) inferInstance (fun t ht => ?_)
        (fun h => hEbot (le_bot_iff.mp (le_sup_left.trans h.le)))
      have h1 : E ≤ (E ⊔ F).comap c.toMonoidHom := fun e he =>
        mem_sup_right (show c (c e) ∈ E by rw [hcc]; exact he)
      have h2 : F ≤ (E ⊔ F).comap c.toMonoidHom := fun f hf => mem_sup_left hf
      exact sup_le h1 h2 ht
    have hDtop : commutator K ≠ ⊤ := by
      intro hDtop
      have haD : a ∈ commutator K := by rw [hDtop]; exact mem_top a
      apply hEbot
      rw [eq_bot_iff, ← hEF]
      intro e he
      refine ⟨he, ?_⟩
      show c e ∈ E
      have hce : c e = ⟨a, haD⟩ * e * (⟨a, haD⟩ : commutator K)⁻¹ := Subtype.ext rfl
      rw [hce]
      exact hE.conj_mem e he _
    have hidx := index_eq_two_of_normal hΩ hm1 hmodd hax ha2 hgen hsimple
      (N := commutator K) inferInstance hDbot hDtop
    have hcompl : IsComplement' E F := isComplement'_of_disjoint_and_mul_eq_univ
      (disjoint_iff.mpr hEF) (by rw [← normal_mul, hsup, coe_top])
    have hFE : Nat.card F = Nat.card E :=
      Nat.card_congr (Equiv.subtypeEquiv c.toEquiv fun _ => Iff.rfl)
    apply hsq (Nat.card E)
    rw [← index_mul_card (commutator K), hidx, ← hcompl.card_mul_card, hFE, sq]
  · have h := key (E ⊓ F) inferInstance hEF_c hEF
    exact eq_top_iff.mpr (h.symm.le.trans inf_le_left)

private theorem injective_conjNormal_commutator [Finite K] [FaithfulSMul K Ω]
    [IsPreprimitive K Ω] {m : ℕ} (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m)
    {x : Ω} {a : K} (hax : a ∈ stabilizer K x) (ha2 : orderOf a = 2)
    (hgen : normalClosure {a} = ⊤) [(zpowers (⟨a, hax⟩ : stabilizer K x)).Normal]
    (hsimple : IsSimpleGroup (stabilizer K x ⧸ zpowers (⟨a, hax⟩ : stabilizer K x))) :
    Function.Injective (MulAut.conjNormal (H := commutator K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hg1
  have hgC : g ∈ centralizer (commutator K : Set K) := by
    rw [mem_centralizer_iff]
    intro d hd
    have h1 := congrArg (fun φ : MulAut (commutator K) => ((φ ⟨d, hd⟩ : commutator K) : K)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hCbot : centralizer (commutator K : Set K) ≠ ⊥ := fun h => hg1 (by
    rw [h, mem_bot] at hgC
    exact hgC)
  have hle := commutator_le_of_normal hΩ hm1 hmodd hax ha2 hgen hsimple inferInstance hCbot
  apply not_isMulCommutative_commutator hΩ hm1 hmodd x ha2
  exact ⟨⟨fun d₁ d₂ => Subtype.ext (mem_centralizer_iff.mp (hle d₂.2) d₁ d₁.2)⟩⟩

theorem primitive_central_involution_simple_stabilizer_quotient {K Ω : Type*} [Group K]
    [Finite K] [MulAction K Ω] [FaithfulSMul K Ω] [IsPreprimitive K Ω] {m : ℕ}
    (hΩ : Nat.card Ω = 2 * m) (hm1 : 1 < m) (hmodd : Odd m) (x : Ω) (a : K)
    (hax : a ∈ stabilizer K x) (ha2 : orderOf a = 2) (hgen : normalClosure {a} = ⊤)
    [(zpowers (⟨a, hax⟩ : stabilizer K x)).Normal]
    (hsimple : IsSimpleGroup (stabilizer K x ⧸ zpowers (⟨a, hax⟩ : stabilizer K x)))
    (hsq : ∀ s : ℕ, Nat.card K ≠ 2 * s ^ 2) :
    (∀ N : Subgroup K, N.Normal → N ≠ ⊥ → N ≠ ⊤ → N.index = 2) ∧
      IsSimpleGroup (commutator K) ∧ ¬ IsMulCommutative (commutator K) ∧
      (∀ N : Subgroup K, N.Normal → N ≠ ⊥ → commutator K ≤ N) ∧
      (commutator K).index ≤ 2 ∧
      Function.Injective (MulAut.conjNormal (H := commutator K)) ∧
      (commutator K ≠ ⊤ →
        a ∉ commutator K ∧
        zpowers a ⊓ (commutator K ⊓ stabilizer K x) = ⊥ ∧
        zpowers a ⊔ (commutator K ⊓ stabilizer K x) = stabilizer K x ∧
        Function.Bijective (fun g : ↥(commutator K ⊓ stabilizer K x) =>
          (QuotientGroup.mk (⟨g, g.2.2⟩ : stabilizer K x) :
            stabilizer K x ⧸ zpowers (⟨a, hax⟩ : stabilizer K x)))) ∧
      ((¬ ∃ U : Subgroup K, U ≤ stabilizer K x ∧ zpowers a ⊓ U = ⊥ ∧
          zpowers a ⊔ U = stabilizer K x) → IsSimpleGroup K) := by
  have hDbot := commutator_ne_bot hΩ hm1 hmodd x ha2
  refine ⟨fun N hN hNbot hNtop =>
      index_eq_two_of_normal hΩ hm1 hmodd hax ha2 hgen hsimple hN hNbot hNtop,
    isSimpleGroup_commutator hΩ hm1 hmodd hax ha2 hgen hsimple hsq,
    not_isMulCommutative_commutator hΩ hm1 hmodd x ha2,
    fun N hN hNbot => commutator_le_of_normal hΩ hm1 hmodd hax ha2 hgen hsimple hN hNbot,
    ?_, injective_conjNormal_commutator hΩ hm1 hmodd hax ha2 hgen hsimple,
    fun hDtop => complement_of_normal hΩ hm1 hmodd hax ha2 hgen hsimple
      (N := commutator K) inferInstance hDbot hDtop, ?_⟩
  · by_cases hDtop : commutator K = ⊤
    · rw [hDtop, index_top]
      omega
    · rw [index_eq_two_of_normal hΩ hm1 hmodd hax ha2 hgen hsimple (N := commutator K)
        inferInstance hDbot hDtop]
  · intro hnot
    have ha1 : a ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ha2
      omega
    have : Nontrivial K := ⟨⟨a, 1, ha1⟩⟩
    rw [isSimpleGroup_iff]
    refine ⟨inferInstance, ?_⟩
    intro N hN
    by_contra hcon
    obtain ⟨hbot, htop⟩ := not_or.mp hcon
    obtain ⟨-, h1, h2, -⟩ := complement_of_normal hΩ hm1 hmodd hax ha2 hgen hsimple hN hbot htop
    exact hnot ⟨_, inf_le_right, h1, h2⟩

end CFSG.Monster.B.Generic
