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
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.G64

open Equiv Equiv.Perm Finset

@[expose] def fiberStab {α ι : Type*} (f : α → ι) : Subgroup (Perm α) where
  carrier := {g | f ∘ g = f}
  one_mem' := by
    show f ∘ ⇑(1 : Perm α) = f
    rw [Perm.coe_one, Function.comp_id]
  mul_mem' := by
    intro g h hg hh
    show f ∘ ⇑(g * h) = f
    rw [Perm.coe_mul, ← Function.comp_assoc]
    rw [show f ∘ ⇑g = f from hg]
    exact hh
  inv_mem' := by
    intro g hg
    show f ∘ ⇑g⁻¹ = f
    funext x
    have := congrFun (show f ∘ ⇑g = f from hg) (g⁻¹ x)
    simpa using this.symm

theorem card_fiberStab {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (f : α → ι) : Nat.card (fiberStab f) = ∏ i, (Fintype.card {a // f a = i}).factorial := by
  rw [← DomMulAct.stabilizer_card f, ← Nat.card_eq_fintype_card]
  rfl

theorem card_dvd_of_preserves {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    [DecidableEq ι] (f : α → ι) {P : Subgroup (Perm α)} (hP : ∀ σ ∈ P, ∀ x, f (σ x) = f x) :
    Nat.card P ∣ ∏ i, (Fintype.card {a // f a = i}).factorial := by
  rw [← card_fiberStab f]
  refine Subgroup.card_dvd_of_le fun σ hσ => ?_
  show f ∘ ⇑σ = f
  funext x
  exact hP σ hσ x

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem isThreeCycle_of_pow_three {σ : Perm α} (h1 : σ ≠ 1) (h3 : σ ^ 3 = 1)
    (hs : #σ.support ≤ 4) : σ.IsThreeCycle := by
  have hmem : ∀ m ∈ σ.cycleType, m = 3 := by
    intro m hm
    have h2 := two_le_of_mem_cycleType hm
    have hd : m ∣ 3 := (dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one h3)
    have hle : m ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases m
    · norm_num at hd
    · rfl
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate.2 ⟨rfl, hmem⟩
  have hsum : (σ.cycleType).sum = 3 * Multiset.card σ.cycleType := by
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]
  rw [sum_cycleType] at hsum
  have hne : σ.cycleType ≠ 0 := fun h => h1 (cycleType_eq_zero.1 h)
  have hcard : Multiset.card σ.cycleType = 1 := by
    have hpos : 0 < Multiset.card σ.cycleType := Multiset.card_pos.2 hne
    omega
  show σ.cycleType = {3}
  rw [hrep, hcard]
  rfl

theorem mem_support_iff_of_mem_normalizer {c σ : Perm α}
    (hσ : σ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set (Perm α))) (x : α) :
    σ x ∈ c.support ↔ x ∈ c.support := by
  have hmem : σ * c * σ⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.1 hσ c).1 (Subgroup.mem_zpowers c)
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hsub : (σ * c * σ⁻¹).support ⊆ c.support := by
    rw [← hz]
    exact support_zpow_le c z
  have hcard : #(σ * c * σ⁻¹).support = #c.support := by
    rw [support_conj, Finset.card_map]
  have heq : (σ * c * σ⁻¹).support = c.support :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  rw [support_conj] at heq
  constructor
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.1 hx
    have : y = x := σ.injective hyx
    rwa [← this]
  · intro hx
    rw [← heq]
    exact Finset.mem_map_of_mem _ hx

theorem eq_or_eq_inv_of_support_eq {c d : Perm α} (hc : c.IsThreeCycle) (hd : d.IsThreeCycle)
    (h : d.support = c.support) : d = c ∨ d = c⁻¹ := by
  obtain ⟨x, hx⟩ : c.support.Nonempty := by
    rw [← Finset.card_pos, hc.card_support]
    norm_num
  have hxd : x ∈ d.support := h ▸ hx
  have hcs := hc.support_eq_iff_mem_support.2 hx
  have hds := hd.support_eq_iff_mem_support.2 hxd
  have hcn := hc.nodup_iff_mem_support.2 hx
  have hdn := hd.nodup_iff_mem_support.2 hxd
  have hc3 : (c ^ 3) x = x := by rw [← hc.orderOf, pow_orderOf_eq_one]; rfl
  have hci : c⁻¹ x = c (c x) := by
    rw [Perm.inv_eq_iff_eq]
    simpa [pow_succ] using hc3.symm
  have hdx : d x ∈ c.support := by
    rw [← h]
    exact (Perm.apply_mem_support).2 hxd
  rw [hcs] at hdx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdx
  have hddx : d (d x) ∈ c.support := by
    rw [← h]
    exact (Perm.apply_mem_support).2 ((Perm.apply_mem_support).2 hxd)
  rw [hcs] at hddx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hddx
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hcn hdn
  rcases hdx with h1 | h1 | h1
  · exact absurd h1.symm hdn.1.1
  · have h2 : d (d x) = c (c x) := by
      rcases hddx with h2 | h2 | h2
      · exact absurd h2.symm hdn.1.2
      · exact absurd (h2.trans h1.symm).symm hdn.2
      · exact h2
    left
    rw [hd.eq_swap_mul_swap_iff_mem_support.2 hxd, hc.eq_swap_mul_swap_iff_mem_support.2 hx, h2,
      h1]
  · have h2 : d (d x) = c x := by
      rcases hddx with h2 | h2 | h2
      · exact absurd h2.symm hdn.1.2
      · exact h2
      · exact absurd (h2.trans h1.symm).symm hdn.2
    right
    have hcinv : c⁻¹.IsThreeCycle := hc.inv
    have hxi : x ∈ c⁻¹.support := by rwa [support_inv]
    have hcii : c⁻¹ (c⁻¹ x) = c x := by
      rw [hci, Perm.inv_eq_iff_eq]
    rw [hd.eq_swap_mul_swap_iff_mem_support.2 hxd, hcinv.eq_swap_mul_swap_iff_mem_support.2 hxi,
      hcii, hci, h2, h1]

theorem card_filter_add_card_filter {β : Type*} [Fintype β] {φ₁ φ₂ ψ : β → Prop}
    [DecidablePred φ₁] [DecidablePred φ₂] [DecidablePred ψ]
    (h : ∀ a, ((if φ₁ a then 1 else 0) + if φ₂ a then 1 else 0) = if ψ a then 1 else 0) :
    #(univ.filter φ₁) + #(univ.filter φ₂) = #(univ.filter ψ) := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => h a

theorem card_decide_mem (s : Finset α) (b : Bool) :
    Fintype.card {a // decide (a ∈ s) = b} = if b then #s else Fintype.card α - #s := by
  cases b
  · simp only [decide_eq_false_iff_not, Bool.false_eq_true, ↓reduceIte]
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  · simp only [decide_eq_true_eq, ↓reduceIte]
    exact Fintype.card_coe s

theorem card_eq_of_sylow {n : ℕ} {P : Subgroup (Perm (Fin n))} (hP : IsPGroup 2 P)
    (hi : ¬ 2 ∣ P.index) :
    ∃ v : ℕ, Nat.card P = 2 ^ v ∧ ∃ m, ¬ 2 ∣ m ∧ 2 ^ v * m = n.factorial := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.1 hP
  refine ⟨v, hv, P.index, hi, ?_⟩
  rw [← hv, Subgroup.card_mul_index, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem false_of_three_cycle {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) {P : Subgroup (Perm (Fin n))}
    (hP : IsPGroup 2 P) (hi : ¬ 2 ∣ P.index) {c : Perm (Fin n)} (hc : c.IsThreeCycle)
    (hPc : P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (Perm (Fin n)))) : False := by
  have hdvd := card_dvd_of_preserves (fun x : Fin n => decide (x ∈ c.support)) (P := P)
    (fun σ hσ x => by simp only [mem_support_iff_of_mem_normalizer (hPc hσ) x])
  rw [Fintype.prod_bool, card_decide_mem, card_decide_mem, hc.card_support] at hdvd
  simp only [↓reduceIte, Bool.false_eq_true, Fintype.card_fin] at hdvd
  obtain ⟨v, hv, m, hm, hvm⟩ := card_eq_of_sylow hP hi
  rw [hv] at hdvd
  have hle : 2 ^ v ≤ (3 : ℕ).factorial * (n - 3).factorial :=
    Nat.le_of_dvd (by positivity) hdvd
  rcases hn with rfl | rfl | rfl
  · norm_num [Nat.factorial] at hle hvm hdvd
    have hv4 : v < 4 := by
      by_contra hcon
      have : 2 ^ 4 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
      omega
    interval_cases v <;> omega
  · norm_num [Nat.factorial] at hle hvm hdvd
    have hv6 : v < 6 := by
      by_contra hcon
      have : 2 ^ 6 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
      omega
    interval_cases v <;> omega
  · norm_num [Nat.factorial] at hle hvm hdvd
    have hv10 : v < 10 := by
      by_contra hcon
      have : 2 ^ 10 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
      omega
    interval_cases v <;> omega

theorem normalizer_le_of_three_cycle {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 P)
    (hi : ¬ 2 ∣ P.index) {c : Perm (Fin 7)} (hc : c.IsThreeCycle)
    (hPc : P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (Perm (Fin 7)))) :
    Subgroup.normalizer (P : Set (Perm (Fin 7))) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set (Perm (Fin 7))) := by
  intro g hg
  set d := g * c * g⁻¹ with hd
  have hdc : d.IsThreeCycle := by
    rw [hd, ← card_support_eq_three_iff, support_conj, Finset.card_map]
    exact hc.card_support
  have hPd : P ≤ Subgroup.normalizer (Subgroup.zpowers d : Set (Perm (Fin 7))) := by
    intro σ hσ
    have hσ' : g⁻¹ * σ * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) σ).1 hσ
      simpa using this
    have hn := hPc hσ'
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h1 := (hn (c ^ z)).1 (Subgroup.zpow_mem_zpowers c z)
      obtain ⟨w, hw⟩ := Subgroup.mem_zpowers_iff.1 h1
      refine Subgroup.mem_zpowers_iff.2 ⟨w, ?_⟩
      rw [hd]
      simp only [conj_zpow]
      rw [hw]
      group
    · intro hx
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hx' : x = σ⁻¹ * d ^ z * σ := by rw [hz]; group
      have h1 : (g⁻¹ * σ * g) * (g⁻¹ * x * g) * (g⁻¹ * σ * g)⁻¹ ∈ Subgroup.zpowers c := by
        refine Subgroup.mem_zpowers_iff.2 ⟨z, ?_⟩
        rw [hx', hd]
        simp only [conj_zpow]
        group
      have h2 := (hn (g⁻¹ * x * g)).2 h1
      obtain ⟨w, hw⟩ := Subgroup.mem_zpowers_iff.1 h2
      refine Subgroup.mem_zpowers_iff.2 ⟨w, ?_⟩
      rw [hd]
      simp only [conj_zpow]
      rw [hw]
      group
  have hsup : d.support = c.support := by
    by_contra hne
    have hpres : ∀ σ ∈ P, ∀ x, (decide (σ x ∈ c.support), decide (σ x ∈ d.support)) =
        (decide (x ∈ c.support), decide (x ∈ d.support)) := fun σ hσ x => by
      simp only [mem_support_iff_of_mem_normalizer (hPc hσ) x,
        mem_support_iff_of_mem_normalizer (hPd hσ) x]
    have hdvd := card_dvd_of_preserves
      (fun x : Fin 7 => (decide (x ∈ c.support), decide (x ∈ d.support))) hpres
    rw [Fintype.prod_prod_type, Fintype.prod_bool, Fintype.prod_bool, Fintype.prod_bool] at hdvd
    simp only [Fintype.card_subtype, Prod.mk.injEq] at hdvd
    have hs3 : #c.support = 3 := hc.card_support
    have ht3 : #d.support = 3 := hdc.card_support
    have hAB : #(univ.filter fun a : Fin 7 =>
          decide (a ∈ c.support) = true ∧ decide (a ∈ d.support) = true) +
        #(univ.filter fun a : Fin 7 =>
          decide (a ∈ c.support) = true ∧ decide (a ∈ d.support) = false) = 3 := by
      rw [card_filter_add_card_filter (ψ := fun a => a ∈ c.support), Finset.filter_mem_eq_inter,
        Finset.univ_inter, hs3]
      intro a
      by_cases ha : a ∈ c.support <;> by_cases hb : a ∈ d.support <;> simp [ha, hb]
    have hAC : #(univ.filter fun a : Fin 7 =>
          decide (a ∈ c.support) = true ∧ decide (a ∈ d.support) = true) +
        #(univ.filter fun a : Fin 7 =>
          decide (a ∈ c.support) = false ∧ decide (a ∈ d.support) = true) = 3 := by
      rw [card_filter_add_card_filter (ψ := fun a => a ∈ d.support), Finset.filter_mem_eq_inter,
        Finset.univ_inter, ht3]
      intro a
      by_cases ha : a ∈ c.support <;> by_cases hb : a ∈ d.support <;> simp [ha, hb]
    have hCD : #(univ.filter fun a : Fin 7 =>
          decide (a ∈ c.support) = false ∧ decide (a ∈ d.support) = true) +
        #(univ.filter fun a : Fin 7 =>
          decide (a ∈ c.support) = false ∧ decide (a ∈ d.support) = false) = 4 := by
      rw [card_filter_add_card_filter (ψ := fun a => a ∉ c.support), Finset.filter_not,
        Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff_of_subset
          (Finset.subset_univ _), hs3, Finset.card_univ, Fintype.card_fin]
      intro a
      by_cases ha : a ∈ c.support <;> by_cases hb : a ∈ d.support <;> simp [ha, hb]
    set A := #(univ.filter fun a : Fin 7 =>
      decide (a ∈ c.support) = true ∧ decide (a ∈ d.support) = true) with hA
    set B := #(univ.filter fun a : Fin 7 =>
      decide (a ∈ c.support) = true ∧ decide (a ∈ d.support) = false)
    set C := #(univ.filter fun a : Fin 7 =>
      decide (a ∈ c.support) = false ∧ decide (a ∈ d.support) = true)
    set D := #(univ.filter fun a : Fin 7 =>
      decide (a ∈ c.support) = false ∧ decide (a ∈ d.support) = false)
    have hA3 : A ≠ 3 := by
      intro hA'
      apply hne
      have hsub : c.support ⊆ d.support := by
        intro a ha
        by_contra hb
        have hB : 0 < B := by
          rw [Finset.card_pos]
          refine ⟨a, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
            decide_eq_false_iff_not]
          exact ⟨ha, hb⟩
        omega
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    obtain ⟨v, hv, m, hm, hvm⟩ := card_eq_of_sylow hP hi
    rw [hv] at hdvd
    norm_num [Nat.factorial] at hvm
    have hv4 : v = 4 := by
      have hv13 : v < 13 := by
        by_contra hcon
        have : 2 ^ 13 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
        have h2 : 2 ^ v ∣ 5040 := ⟨m, hvm.symm⟩
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      interval_cases v <;> omega
    subst hv4
    have hA' : A ≤ 3 := by omega
    interval_cases A
    · have hB : B = 3 := by omega
      have hC : C = 3 := by omega
      have hD : D = 1 := by omega
      rw [hB, hC, hD] at hdvd
      norm_num [Nat.factorial] at hdvd
    · have hB : B = 2 := by omega
      have hC : C = 2 := by omega
      have hD : D = 2 := by omega
      rw [hB, hC, hD] at hdvd
      norm_num [Nat.factorial] at hdvd
    · have hB : B = 1 := by omega
      have hC : C = 1 := by omega
      have hD : D = 3 := by omega
      rw [hB, hC, hD] at hdvd
      norm_num [Nat.factorial] at hdvd
    · exact absurd rfl hA3
  have hdc' := eq_or_eq_inv_of_support_eq hc hdc hsup
  have hd' : g * c * g⁻¹ ∈ Subgroup.zpowers c := by
    rcases hdc' with h | h
    · rw [← hd, h]; exact Subgroup.mem_zpowers c
    · rw [← hd, h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)
  have hd'' : g⁻¹ * c * g ∈ Subgroup.zpowers c := by
    rcases hdc' with h | h
    · have : g⁻¹ * c * g = c := by
        rw [hd] at h
        calc g⁻¹ * c * g = g⁻¹ * (g * c * g⁻¹) * g := by rw [h]
          _ = c := by group
      rw [this]; exact Subgroup.mem_zpowers c
    · have : g⁻¹ * c * g = c⁻¹ := by
        rw [hd] at h
        have h' : g * c⁻¹ * g⁻¹ = c := by
          rw [show g * c⁻¹ * g⁻¹ = (g * c * g⁻¹)⁻¹ by group, h, inv_inv]
        calc g⁻¹ * c * g = g⁻¹ * (g * c⁻¹ * g⁻¹) * g := by rw [h']
          _ = c⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hd' z
  · intro hx
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : x = (g⁻¹ * c * g) ^ z := by
      rw [show g⁻¹ * c * g = g⁻¹ * c * g⁻¹⁻¹ by group, conj_zpow, hz]
      group
    rw [this]
    exact Subgroup.zpow_mem _ hd'' z

end CFSG.Quasithin.G64
