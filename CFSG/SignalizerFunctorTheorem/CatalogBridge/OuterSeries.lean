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
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem le_normalCore_of_index_le_three {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hidx : E.index ≤ 3) {r : ℕ} (hr3 : 3 < r) {P : Subgroup G} (hP : IsPGroup r P)
    [Fact r.Prime] : P ≤ E.normalCore := by
  intro x hx
  show ∀ g : G, g * x * g⁻¹ ∈ E
  intro g
  set y : G ⧸ E := (QuotientGroup.mk (g⁻¹) : G ⧸ E) with hy
  obtain ⟨n, hn⟩ := hP.card_orbit y
  have hle : Nat.card (MulAction.orbit P y) ≤ 3 := by
    refine (Nat.card_le_card_of_injective (Subtype.val : MulAction.orbit P y → G ⧸ E)
      Subtype.val_injective).trans ?_
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hn0 : n = 0 := by
    by_contra hne
    have := Nat.le_self_pow hne r
    omega
  rw [hn0, pow_zero] at hn
  have h1 : Nat.card (MulAction.orbit P y) = 1 := hn
  rw [Nat.card_eq_one_iff_unique] at h1
  obtain ⟨hsub, -⟩ := h1
  have h2 : (⟨(⟨x, hx⟩ : P) • y, MulAction.mem_orbit y _⟩ : MulAction.orbit P y) =
      ⟨y, MulAction.mem_orbit_self y⟩ := Subsingleton.elim _ _
  have h3 : x • y = y := congrArg Subtype.val h2
  have h4 : ((x * g⁻¹ : G) : G ⧸ E) = ((g⁻¹ : G) : G ⧸ E) := h3
  rw [QuotientGroup.eq] at h4
  have h5 : g * x⁻¹ * g⁻¹ ∈ E := by simpa [mul_assoc] using h4
  have h6 := E.inv_mem h5
  simpa [mul_assoc] using h6

theorem conj_eq_of_isPGroup {G : Type*} [Group G] [Finite G] {E O : Subgroup G}
    (hOE : ∀ e ∈ E, ∀ o ∈ O, e * o * e⁻¹ ∈ O) (hO4 : Nat.card O ≤ 4) {r : ℕ} (hr3 : 3 < r)
    [Fact r.Prime] {P : Subgroup G} (hP : IsPGroup r P) (hPE : P ≤ E) {g : G} (hg : g ∈ P)
    {o : G} (ho : o ∈ O) : g * o * g⁻¹ = o := by
  classical
  let ψ : P →* Equiv.Perm O :=
    { toFun := fun h =>
        { toFun := fun x => ⟨h * x * (h : G)⁻¹, hOE h (hPE h.2) x x.2⟩
          invFun := fun x => ⟨(h : G)⁻¹ * x * h, by
            have := hOE (h⁻¹ : G) (E.inv_mem (hPE h.2)) x x.2
            simpa using this⟩
          left_inv := fun x => Subtype.ext (by simp [mul_assoc])
          right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
      map_one' := Equiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun a b => Equiv.ext fun x => Subtype.ext (by
        simp [mul_assoc]) }
  have hr4 : r ≠ 4 := by
    rintro rfl
    exact absurd (Fact.out : Nat.Prime 4) (by norm_num)
  have hψ : ψ ⟨g, hg⟩ = 1 := by
    have h1 : orderOf (ψ ⟨g, hg⟩) ∣ Nat.card P :=
      (orderOf_map_dvd ψ ⟨g, hg⟩).trans (orderOf_dvd_natCard _)
    have : Fintype O := Fintype.ofFinite O
    have h2 : orderOf (ψ ⟨g, hg⟩) ∣ (Nat.card O).factorial := by
      have := orderOf_dvd_natCard (ψ ⟨g, hg⟩)
      rwa [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card] at this
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hcop : Nat.Coprime (Nat.card P) (Nat.card O).factorial := by
      rw [hk]
      refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 ?_)
      intro hd
      have := (Nat.Prime.dvd_factorial (Fact.out)).1 hd
      omega
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have h3 := congrArg (fun e : Equiv.Perm O => ((e ⟨o, ho⟩ : O) : G)) hψ
  exact h3

theorem outerSeries_trivial {G : Type*} [Group G] [Finite G] (E D O : Subgroup G) (hDE : D ≤ E)
    (hidx : E.index ≤ 3) (hEab : ⁅E, E⁆ ≤ D)
    (hOE : ∀ e ∈ E, ∀ o ∈ O, e * o * e⁻¹ ∈ O) (hO4 : Nat.card O ≤ 4)
    (hDO : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ∈ O ∨ d₂ ∈ O ∨ d₁⁻¹ * d₂ ∈ O)
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) {P Q : Subgroup G} (hP : IsPGroup r P)
    (hQP : ⁅Q, P⁆ = Q) : Q = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  have hPcore : P ≤ E.normalCore := le_normalCore_of_index_le_three hidx hr3 hP
  have hPE : P ≤ E := hPcore.trans (Subgroup.normalCore_le E)
  have hQcore : Q ≤ E.normalCore := by
    rw [← hQP]
    refine Subgroup.commutator_le.2 fun q hq p hp => ?_
    have hpc : p ∈ E.normalCore := hPcore hp
    have h1 : q * p * q⁻¹ ∈ E.normalCore := (E.normalCore_normal.conj_mem p hpc q)
    have : ⁅q, p⁆ = (q * p * q⁻¹) * p⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact E.normalCore.mul_mem h1 (E.normalCore.inv_mem hpc)
  have hQE : Q ≤ E := hQcore.trans (Subgroup.normalCore_le E)
  have hQD : Q ≤ D := by
    rw [← hQP]
    exact Subgroup.commutator_le.2 fun q hq p hp =>
      hEab (Subgroup.commutator_mem_commutator (hQE hq) (hPE hp))
  have hcentral : ∀ g ∈ P, ∀ d ∈ D, g * d * g⁻¹ = d := by
    intro g hg d hd
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hgE : g ∈ E := hPE hg
    have hd' : g * d * g⁻¹ ∈ D := by
      have : g * d * g⁻¹ = ⁅g, d⁆ * d := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact D.mul_mem (hEab (Subgroup.commutator_mem_commutator hgE (hDE hd))) hd
    set c : G := g * d * g⁻¹ * d⁻¹ with hc
    have hcd : g * d * g⁻¹ = c * d := by simp [hc]
    have hcO : c ∈ O := by
      rcases hDO d hd (g * d * g⁻¹) hd' with h | h | h
      · have := hOE g hgE d h
        exact O.mul_mem this (O.inv_mem h)
      · have := hOE g⁻¹ (E.inv_mem hgE) _ h
        have hdO : d ∈ O := by simpa [mul_assoc] using this
        exact O.mul_mem h (O.inv_mem hdO)
      · have hh : c = d * (d⁻¹ * (g * d * g⁻¹)) * d⁻¹ := by simp [hc, mul_assoc]
        rw [hh]
        exact hOE d (hDE hd) _ h
    have hgc : g * c * g⁻¹ = c := conj_eq_of_isPGroup hOE hO4 hr3 hP hPE hg hcO
    have hpow : ∀ n : ℕ, g ^ n * d * (g ^ n)⁻¹ = c ^ n * d := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h1 : g ^ (n + 1) * d * (g ^ (n + 1))⁻¹ = g * (g ^ n * d * (g ^ n)⁻¹) * g⁻¹ := by
          simp [pow_succ', mul_assoc]
        rw [h1, ih]
        have h2 : g * (c ^ n * d) * g⁻¹ = (g * c * g⁻¹) ^ n * (g * d * g⁻¹) := by
          rw [conj_pow]
          group
        have h3 : c ^ n * (c * d) = c ^ (n + 1) * d := by
          rw [pow_succ]
          exact (mul_assoc _ _ _).symm
        rw [h2, hgc, hcd]
        exact h3
    have hg1 : g ^ Nat.card P = 1 := by
      have := pow_card_eq_one' (x := (⟨g, hg⟩ : P))
      exact congrArg Subtype.val this
    have hcm : c ^ Nat.card P = 1 := by
      have := hpow (Nat.card P)
      rw [hg1] at this
      simpa using this.symm
    have hc1 : c = 1 := by
      have h1 : orderOf c ∣ Nat.card P := orderOf_dvd_of_pow_eq_one hcm
      have h2 : orderOf c ∣ Nat.card O := by
        have := orderOf_dvd_natCard (⟨c, hcO⟩ : O)
        rwa [Subgroup.orderOf_mk] at this
      have hcop : Nat.Coprime (Nat.card P) (Nat.card O) := by
        rw [hk]
        refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).2 ?_)
        intro hd0
        have hpos : 0 < Nat.card O := Nat.card_pos
        have := Nat.le_of_dvd hpos hd0
        have hr4 : r ≠ 4 := by
          rintro rfl
          exact absurd hr (by norm_num)
        omega
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    rw [hcd, hc1, one_mul]
  rw [eq_bot_iff, ← hQP]
  refine Subgroup.commutator_le.2 fun q hq p hp => ?_
  have h1 := hcentral p hp q (hQD hq)
  have : ⁅q, p⁆ = 1 := by
    rw [commutatorElement_def]
    have h2 : q * p = p * q := by
      calc q * p = (p * q * p⁻¹) * p := by rw [h1]
        _ = p * q := by group
    rw [h2]
    group
  rw [this]
  exact Subgroup.one_mem _

end CFSG.SignalizerFunctorTheorem.CatalogBridge
