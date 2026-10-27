module

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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.RankThree.PartOne.KCNilpotent

open Module

section

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem finrank_le_finrank_map_add_finrank_ker [FiniteDimensional k V] (f : V →ₗ[k] V)
    (W : Submodule k V) :
    finrank k W ≤ finrank k (W.map f) + finrank k (LinearMap.ker f) := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict W)
  rw [LinearMap.range_domRestrict] at h
  have hle : finrank k (LinearMap.ker (f.domRestrict W)) ≤ finrank k (LinearMap.ker f) := by
    rw [LinearMap.ker_domRestrict]
    have hinj : Function.Injective (W.subtype.restrict (p := (LinearMap.ker f).comap W.subtype)
        (q := LinearMap.ker f) (fun x hx => hx)) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hxy
    exact LinearMap.finrank_le_finrank_of_injective hinj
  omega

theorem finrank_le_mul_finrank_ker [FiniteDimensional k V] (f : V →ₗ[k] V) {m : ℕ}
    (hf : f ^ m = 0) : finrank k V ≤ m * finrank k (LinearMap.ker f) := by
  have key : ∀ j : ℕ, finrank k V ≤
      finrank k (LinearMap.range (f ^ j)) + j * finrank k (LinearMap.ker f) := by
    intro j
    induction j with
    | zero => rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, finrank_top]; simp
    | succ j ih =>
      have h := finrank_le_finrank_map_add_finrank_ker f (LinearMap.range (f ^ j))
      have hmap : (LinearMap.range (f ^ j)).map f = LinearMap.range (f ^ (j + 1)) := by
        rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
      rw [hmap] at h
      rw [Nat.succ_mul]
      omega
  have := key m
  rw [hf, LinearMap.range_zero, finrank_bot] at this
  omega

theorem exists_mem_ker_not_mem_span (f : V →ₗ[k] V) (s : Finset V)
    (h : s.card < finrank k (LinearMap.ker f)) :
    ∃ w ∈ LinearMap.ker f, w ∉ Submodule.span k (s : Set V) := by
  by_contra hcon
  push Not at hcon
  have hle : LinearMap.ker f ≤ Submodule.span k (s : Set V) := hcon
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_finset_le_card (R := k) s
  have : finrank k (Submodule.span k (s : Set V)) ≤ s.card := h2
  omega

theorem coeff_eq_zero_of_not_mem_span {x w : V} (hw : w ∉ Submodule.span k ({x} : Set V))
    {a b : k} (h : a • x + b • w = 0) : b = 0 := by
  by_contra hb
  apply hw
  rw [Submodule.mem_span_singleton]
  refine ⟨-(b⁻¹ * a), ?_⟩
  have h' : b • w = -(a • x) := eq_neg_of_add_eq_zero_right h
  calc (-(b⁻¹ * a)) • x = b⁻¹ • (-(a • x)) := by rw [neg_smul, mul_smul, smul_neg]
    _ = b⁻¹ • (b • w) := by rw [h']
    _ = w := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem coeff_eq_zero_of_not_mem_span_pair {x y w : V}
    (hw : w ∉ Submodule.span k ({x, y} : Set V)) {a b c : k}
    (h : a • x + b • y + c • w = 0) : c = 0 := by
  by_contra hc
  apply hw
  rw [Submodule.mem_span_pair]
  refine ⟨-(c⁻¹ * a), -(c⁻¹ * b), ?_⟩
  have h' : c • w = -(a • x + b • y) := eq_neg_of_add_eq_zero_right h
  calc (-(c⁻¹ * a)) • x + (-(c⁻¹ * b)) • y = c⁻¹ • (-(a • x + b • y)) := by
        rw [neg_smul, neg_smul, mul_smul, mul_smul, smul_neg, smul_add, neg_add]
    _ = c⁻¹ • (c • w) := by rw [h']
    _ = w := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem linearIndependent_regular_three (f : V →ₗ[k] V) {x₀ x₁ x₂ : V} (hx₀ : x₀ ≠ 0)
    (h₀ : f x₀ = 0) (h₁ : f x₁ = x₀) (h₂ : f x₂ = x₁) :
    LinearIndependent k ![x₀, x₁, x₂] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have e1 := congrArg f hg
  simp only [map_add, map_smul, map_zero, h₀, h₁, h₂, smul_zero, zero_add] at e1
  have e2 := congrArg f e1
  simp only [map_add, map_smul, map_zero, h₀, h₁, smul_zero, zero_add] at e2
  have g2 : g 2 = 0 := (smul_eq_zero.mp e2).resolve_right hx₀
  rw [g2, zero_smul, add_zero] at e1
  have g1 : g 1 = 0 := (smul_eq_zero.mp e1).resolve_right hx₀
  rw [g1, g2, zero_smul, zero_smul, add_zero, add_zero] at hg
  have g0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hx₀
  intro i
  fin_cases i <;> simp [g0, g1, g2]

theorem linearIndependent_regular_four (f : V →ₗ[k] V) {x₀ x₁ x₂ x₃ : V} (hx₀ : x₀ ≠ 0)
    (h₀ : f x₀ = 0) (h₁ : f x₁ = x₀) (h₂ : f x₂ = x₁) (h₃ : f x₃ = x₂) :
    LinearIndependent k ![x₀, x₁, x₂, x₃] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have e1 := congrArg f hg
  simp only [map_add, map_smul, map_zero, h₀, h₁, h₂, h₃, smul_zero, zero_add] at e1
  have e2 := congrArg f e1
  simp only [map_add, map_smul, map_zero, h₀, h₁, h₂, smul_zero, zero_add] at e2
  have e3 := congrArg f e2
  simp only [map_add, map_smul, map_zero, h₀, h₁, smul_zero, zero_add] at e3
  have g3 : g 3 = 0 := (smul_eq_zero.mp e3).resolve_right hx₀
  rw [g3, zero_smul, add_zero] at e2
  have g2 : g 2 = 0 := (smul_eq_zero.mp e2).resolve_right hx₀
  rw [g2, g3, zero_smul, zero_smul, add_zero, add_zero] at e1
  have g1 : g 1 = 0 := (smul_eq_zero.mp e1).resolve_right hx₀
  rw [g1, g2, g3, zero_smul, zero_smul, zero_smul, add_zero, add_zero, add_zero] at hg
  have g0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hx₀
  intro i
  fin_cases i <;> simp [g0, g1, g2, g3]

theorem linearIndependent_three_two (f : V →ₗ[k] V) {x₀ w v : V} (hx₀ : x₀ ≠ 0)
    (h₀ : f x₀ = 0) (hw : f w = 0) (hv : f v = x₀)
    (hwn : w ∉ Submodule.span k ({x₀} : Set V)) : LinearIndependent k ![x₀, w, v] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have e1 := congrArg f hg
  simp only [map_add, map_smul, map_zero, h₀, hw, hv, smul_zero, zero_add, add_zero] at e1
  have g2 : g 2 = 0 := (smul_eq_zero.mp e1).resolve_right hx₀
  rw [g2, zero_smul, add_zero] at hg
  have g1 : g 1 = 0 := coeff_eq_zero_of_not_mem_span hwn hg
  rw [g1, zero_smul, add_zero] at hg
  have g0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hx₀
  intro i
  fin_cases i <;> simp [g0, g1, g2]

theorem linearIndependent_four_one (f : V →ₗ[k] V) {x₀ u₁ u₂ v : V} (hx₀ : x₀ ≠ 0)
    (h₀ : f x₀ = 0) (hu₁ : f u₁ = 0) (hu₂ : f u₂ = 0) (hv : f v = x₀)
    (hn₁ : u₁ ∉ Submodule.span k ({x₀} : Set V))
    (hn₂ : u₂ ∉ Submodule.span k ({x₀, u₁} : Set V)) :
    LinearIndependent k ![x₀, u₁, u₂, v] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have e1 := congrArg f hg
  simp only [map_add, map_smul, map_zero, h₀, hu₁, hu₂, hv, smul_zero, zero_add, add_zero] at e1
  have g3 : g 3 = 0 := (smul_eq_zero.mp e1).resolve_right hx₀
  rw [g3, zero_smul, add_zero] at hg
  have g2 : g 2 = 0 := coeff_eq_zero_of_not_mem_span_pair hn₂ hg
  rw [g2, zero_smul, add_zero] at hg
  have g1 : g 1 = 0 := coeff_eq_zero_of_not_mem_span hn₁ hg
  rw [g1, zero_smul, add_zero] at hg
  have g0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hx₀
  intro i
  fin_cases i <;> simp [g0, g1, g2, g3]

theorem linearIndependent_two_two (f : V →ₗ[k] V) {x₀ x₁ v v' : V} (hx₀ : x₀ ≠ 0)
    (h₀ : f x₀ = 0) (h₁ : f x₁ = 0) (hv : f v = x₀) (hv' : f v' = x₁)
    (hn : x₁ ∉ Submodule.span k ({x₀} : Set V)) :
    LinearIndependent k ![x₀, x₁, v, v'] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have e1 := congrArg f hg
  simp only [map_add, map_smul, map_zero, h₀, h₁, hv, hv', smul_zero, zero_add] at e1
  have g3 : g 3 = 0 := coeff_eq_zero_of_not_mem_span hn e1
  rw [g3, zero_smul, add_zero] at e1
  have g2 : g 2 = 0 := (smul_eq_zero.mp e1).resolve_right hx₀
  rw [g3, g2, zero_smul, zero_smul, add_zero, add_zero] at hg
  have g1 : g 1 = 0 := coeff_eq_zero_of_not_mem_span hn hg
  rw [g1, zero_smul, add_zero] at hg
  have g0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hx₀
  intro i
  fin_cases i <;> simp [g0, g1, g2, g3]

theorem linearIndependent_three_one (f : V →ₗ[k] V) {x₀ x₁ x₂ w : V} (hx₀ : x₀ ≠ 0)
    (h₀ : f x₀ = 0) (h₁ : f x₁ = x₀) (h₂ : f x₂ = x₁) (hw : f w = 0)
    (hwn : w ∉ Submodule.span k ({x₀} : Set V)) :
    LinearIndependent k ![x₀, x₁, x₂, w] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have e1 := congrArg f hg
  simp only [map_add, map_smul, map_zero, h₀, h₁, h₂, hw, smul_zero, zero_add, add_zero] at e1
  have e2 := congrArg f e1
  simp only [map_add, map_smul, map_zero, h₀, h₁, smul_zero, zero_add] at e2
  have g2 : g 2 = 0 := (smul_eq_zero.mp e2).resolve_right hx₀
  rw [g2, zero_smul, add_zero] at e1
  have g1 : g 1 = 0 := (smul_eq_zero.mp e1).resolve_right hx₀
  rw [g1, g2, zero_smul, zero_smul, add_zero, add_zero] at hg
  have g3 : g 3 = 0 := coeff_eq_zero_of_not_mem_span hwn hg
  rw [g3, zero_smul, add_zero] at hg
  have g0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hx₀
  intro i
  fin_cases i <;> simp [g0, g1, g2, g3]

end

section

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem exists_chain_three (hdim : finrank k V = 3) (f : V →ₗ[k] V) (hf : f ^ 3 = 0)
    (hne : f ≠ 0) :
    ∃ c : Fin 3 → V, LinearIndependent k c ∧
      ((f (c 0) = 0 ∧ f (c 1) = c 0 ∧ f (c 2) = c 1) ∨
        (f (c 0) = 0 ∧ f (c 1) = 0 ∧ f (c 2) = c 0)) := by
  have hpow : ∀ (m : ℕ) (v : V), (f ^ (m + 1)) v = f ((f ^ m) v) := fun m v => by
    rw [pow_succ', Module.End.mul_apply]
  by_cases h2 : f ^ 2 = 0
  · obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (LinearMap.ext hcon)
    have hff : f (f v) = 0 := by
      have := congrArg (fun g => g v) h2
      simpa [hpow 1 v] using this
    have hker : 2 ≤ finrank k (LinearMap.ker f) := by
      have := finrank_le_mul_finrank_ker f h2
      omega
    obtain ⟨w, hw, hwn⟩ := exists_mem_ker_not_mem_span f {f v} (by
      have := Finset.card_singleton (f v)
      omega)
    have hw0 : f w = 0 := hw
    refine ⟨![f v, w, v], ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · exact linearIndependent_three_two f hv hff hw0 rfl (by simpa using hwn)
    · simpa using hff
    · simpa using hw0
    · simp
  · obtain ⟨v, hv⟩ : ∃ v, (f ^ 2) v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h2 (LinearMap.ext hcon)
    have e1 : (f ^ 2) v = f (f v) := by
      have := hpow 1 v
      simpa using this
    have e0 : f ((f ^ 2) v) = 0 := by
      rw [← hpow 2 v, hf]
      rfl
    refine ⟨![(f ^ 2) v, f v, v], ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
    · exact linearIndependent_regular_three f hv e0 e1.symm rfl
    · simpa using e0
    · simpa using e1.symm
    · simp

theorem exists_chain_four (hdim : finrank k V = 4) (f : V →ₗ[k] V) (hf : f ^ 4 = 0)
    (hne : f ≠ 0) :
    ∃ c : Fin 4 → V, LinearIndependent k c ∧
      ((f (c 0) = 0 ∧ f (c 1) = c 0 ∧ f (c 2) = c 1 ∧ f (c 3) = c 2) ∨
        (f (c 0) = 0 ∧ f (c 1) = 0 ∧ f (c 2) = 0 ∧ f (c 3) = c 0) ∨
        (f (c 0) = 0 ∧ f (c 1) = 0 ∧ f (c 2) = c 0 ∧ f (c 3) = c 1) ∨
        (f (c 0) = 0 ∧ f (c 1) = c 0 ∧ f (c 2) = c 1 ∧ f (c 3) = 0)) := by
  classical
  have hpow : ∀ (m : ℕ) (v : V), (f ^ (m + 1)) v = f ((f ^ m) v) := fun m v => by
    rw [pow_succ', Module.End.mul_apply]
  have hp1 : ∀ v : V, (f ^ 2) v = f (f v) := fun v => by
    have := hpow 1 v
    simpa using this
  by_cases h3 : f ^ 3 = 0
  · by_cases h2 : f ^ 2 = 0
    · obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hne (LinearMap.ext hcon)
      have hff : ∀ u : V, f (f u) = 0 := fun u => by
        have := congrArg (fun g => g u) h2
        simpa [hp1 u] using this
      by_cases hC : ∃ v', f v' ∉ Submodule.span k ({f v} : Set V)
      · obtain ⟨v', hv'⟩ := hC
        refine ⟨![f v, f v', v, v'], linearIndependent_two_two f hv (hff v) (hff v') rfl rfl hv',
          Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩))⟩ <;> simp [hff]
      · push Not at hC
        have hrange : LinearMap.range f ≤ Submodule.span k ({f v} : Set V) := by
          rintro _ ⟨u, rfl⟩
          exact hC u
        have hr : finrank k (LinearMap.range f) ≤ 1 := by
          have h1 := Submodule.finrank_mono hrange
          have h2 := finrank_span_singleton (K := k) hv
          omega
        have hker : 3 ≤ finrank k (LinearMap.ker f) := by
          have := LinearMap.finrank_range_add_finrank_ker f
          omega
        obtain ⟨u₁, hu₁, hu₁n⟩ := exists_mem_ker_not_mem_span f {f v} (by
          have := Finset.card_singleton (f v)
          omega)
        obtain ⟨u₂, hu₂, hu₂n⟩ := exists_mem_ker_not_mem_span f {f v, u₁} (by
          have := Finset.card_le_two (a := f v) (b := u₁)
          omega)
        refine ⟨![f v, u₁, u₂, v], linearIndependent_four_one f hv (hff v) hu₁ hu₂ rfl
          (by simpa using hu₁n) (by simpa using hu₂n),
          Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩)⟩ <;> simp [hff, LinearMap.mem_ker.mp hu₁,
            LinearMap.mem_ker.mp hu₂]
    · obtain ⟨v, hv⟩ : ∃ v, (f ^ 2) v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact h2 (LinearMap.ext hcon)
      have hker : 2 ≤ finrank k (LinearMap.ker f) := by
        have := finrank_le_mul_finrank_ker f h3
        omega
      obtain ⟨w, hw, hwn⟩ := exists_mem_ker_not_mem_span f {(f ^ 2) v} (by
        have := Finset.card_singleton ((f ^ 2) v)
        omega)
      have e0 : f ((f ^ 2) v) = 0 := by
        rw [← hpow 2 v, h3]
        rfl
      have hw0 : f w = 0 := hw
      refine ⟨![(f ^ 2) v, f v, v, w], linearIndependent_three_one f hv e0 (hp1 v).symm rfl hw0
        (by simpa using hwn), Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩))⟩
      · simpa using e0
      · simpa using (hp1 v).symm
      · simp
      · simpa using hw0
  · obtain ⟨v, hv⟩ : ∃ v, (f ^ 3) v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h3 (LinearMap.ext hcon)
    have e0 : f ((f ^ 3) v) = 0 := by
      rw [← hpow 3 v, hf]
      rfl
    have e1 : f ((f ^ 2) v) = (f ^ 3) v := (hpow 2 v).symm
    have e2 : f (f v) = (f ^ 2) v := (hp1 v).symm
    refine ⟨![(f ^ 3) v, (f ^ 2) v, f v, v], linearIndependent_regular_four f hv e0 e1 e2 rfl,
      Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
    · simpa using e0
    · simpa using e1
    · simpa using e2
    · simp

end

end CFSG.RankThree.PartOne.KCNilpotent
