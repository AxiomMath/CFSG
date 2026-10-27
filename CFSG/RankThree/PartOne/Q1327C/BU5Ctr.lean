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

namespace CFSG.RankThree.PartOne.Q1327C

variable {M : Type*} [Group M]

theorem commutator_mul_of_central {Zs : Subgroup M} (hZc : ∀ z ∈ Zs, ∀ g : M, g * z = z * g)
    (ℓ y y' : M) (hy' : ℓ * y' * ℓ⁻¹ * y'⁻¹ ∈ Zs) :
    ℓ * (y * y') * ℓ⁻¹ * (y * y')⁻¹ = (ℓ * y * ℓ⁻¹ * y⁻¹) * (ℓ * y' * ℓ⁻¹ * y'⁻¹) := by
  set c' := ℓ * y' * ℓ⁻¹ * y'⁻¹ with hc'
  have h1 : ℓ * y' * ℓ⁻¹ = c' * y' := by rw [hc']; group
  calc ℓ * (y * y') * ℓ⁻¹ * (y * y')⁻¹
      = (ℓ * y * ℓ⁻¹) * (ℓ * y' * ℓ⁻¹) * y'⁻¹ * y⁻¹ := by group
    _ = (ℓ * y * ℓ⁻¹) * (c' * y') * y'⁻¹ * y⁻¹ := by rw [h1]
    _ = (ℓ * y * ℓ⁻¹) * (c' * y⁻¹) := by group
    _ = (ℓ * y * ℓ⁻¹) * (y⁻¹ * c') := by rw [hZc c' hy' y⁻¹]
    _ = (ℓ * y * ℓ⁻¹ * y⁻¹) * c' := by group

theorem commutator_conj_inverted {Zs : Subgroup M} (hZc : ∀ z ∈ Zs, ∀ g : M, g * z = z * g)
    {ℓ y n : M} (hn : n * ℓ * n⁻¹ * ℓ ∈ Zs) (hy : ℓ * y * ℓ⁻¹ * y⁻¹ ∈ Zs)
    (hu : ℓ * (n * y * n⁻¹) * ℓ⁻¹ * (n * y * n⁻¹)⁻¹ ∈ Zs) :
    ℓ * y * ℓ⁻¹ * y⁻¹ = (ℓ * (n * y * n⁻¹) * ℓ⁻¹ * (n * y * n⁻¹)⁻¹)⁻¹ := by
  set c := ℓ * y * ℓ⁻¹ * y⁻¹ with hc
  set u := n * y * n⁻¹ with hu'
  set cu := ℓ * u * ℓ⁻¹ * u⁻¹ with hcu
  set z₁ := n * ℓ * n⁻¹ * ℓ with hz₁
  have hnc : n * c * n⁻¹ = c := by
    have := hZc c hy n
    calc n * c * n⁻¹ = (c * n) * n⁻¹ := by rw [this]
      _ = c := by group
  have hA : n * ℓ * n⁻¹ = z₁ * ℓ⁻¹ := by rw [hz₁]; group
  have h1 : n * c * n⁻¹ = (n * ℓ * n⁻¹) * u * (n * ℓ * n⁻¹)⁻¹ * u⁻¹ := by
    rw [hc, hu']; group
  have h2 : (z₁ * ℓ⁻¹) * u * (z₁ * ℓ⁻¹)⁻¹ * u⁻¹ = (z₁ * (ℓ⁻¹ * u * ℓ) * z₁⁻¹) * u⁻¹ := by group
  have h3 : z₁ * (ℓ⁻¹ * u * ℓ) * z₁⁻¹ = ℓ⁻¹ * u * ℓ := by
    have := hZc z₁ hn (ℓ⁻¹ * u * ℓ)
    calc z₁ * (ℓ⁻¹ * u * ℓ) * z₁⁻¹ = (ℓ⁻¹ * u * ℓ) * z₁ * z₁⁻¹ := by rw [this]
      _ = ℓ⁻¹ * u * ℓ := by group
  have h4 : ℓ⁻¹ * u * ℓ * u⁻¹ = cu⁻¹ := by
    have e1 : ℓ⁻¹ * u * ℓ * u⁻¹ = ℓ⁻¹ * cu⁻¹ * ℓ := by rw [hcu]; group
    have e2 := hZc cu⁻¹ (Subgroup.inv_mem _ hu) ℓ⁻¹
    rw [e1]
    calc ℓ⁻¹ * cu⁻¹ * ℓ = (cu⁻¹ * ℓ⁻¹) * ℓ := by rw [e2]
      _ = cu⁻¹ := by group
  rw [← hnc, h1, hA, h2, h3, h4]

theorem comm_eq_one_of_inverted {Zs : Subgroup M} (hZc : ∀ z ∈ Zs, ∀ g : M, g * z = z * g)
    (hZ5 : ∀ z ∈ Zs, z ^ 5 = 1) {ℓ y n : M} (hn : n * ℓ * n⁻¹ * ℓ ∈ Zs)
    (hy : ℓ * y * ℓ⁻¹ * y⁻¹ ∈ Zs) (hu : ℓ * (n * y * n⁻¹) * ℓ⁻¹ * (n * y * n⁻¹)⁻¹ ∈ Zs)
    (j : ℤ) (hj : y * (n * y * n⁻¹)⁻¹ * (ℓ ^ j)⁻¹ ∈ Zs) : ℓ * y * ℓ⁻¹ * y⁻¹ = 1 := by
  set u := n * y * n⁻¹ with hu'
  set c := ℓ * y * ℓ⁻¹ * y⁻¹ with hc
  set cu := ℓ * u * ℓ⁻¹ * u⁻¹ with hcu
  have hinv : c = cu⁻¹ := by
    rw [hc, hcu]
    exact commutator_conj_inverted hZc hn hy hu
  have hz : y * u⁻¹ * (ℓ ^ j)⁻¹ ∈ Zs := hj
  set z := y * u⁻¹ * (ℓ ^ j)⁻¹ with hzdef
  have hyu : y * u⁻¹ = z * ℓ ^ j := by rw [hzdef]; group
  have hc1 : ℓ * (y * u⁻¹) * ℓ⁻¹ * (y * u⁻¹)⁻¹ = 1 := by
    rw [hyu]
    have e := hZc z hz ℓ
    have e2 : ℓ * (z * ℓ ^ j) * ℓ⁻¹ * (z * ℓ ^ j)⁻¹ = (ℓ * z) * ℓ ^ j * ℓ⁻¹ * (ℓ ^ j)⁻¹ * z⁻¹ := by
      group
    rw [e2, e]
    group
  have hmul : ℓ * (y * u⁻¹ * u) * ℓ⁻¹ * (y * u⁻¹ * u)⁻¹ =
      (ℓ * (y * u⁻¹) * ℓ⁻¹ * (y * u⁻¹)⁻¹) * (ℓ * u * ℓ⁻¹ * u⁻¹) :=
    commutator_mul_of_central hZc ℓ (y * u⁻¹) u hu
  have hyy : y * u⁻¹ * u = y := by group
  rw [hyy, hc1, one_mul] at hmul
  have hcc : c = cu := hmul
  have hc2 : c * c = 1 := by
    have h1 : c * c = c * cu⁻¹ := by rw [← hinv]
    rw [h1, hcc]
    group
  have hcmem : c ∈ Zs := hy
  have h5 := hZ5 c hcmem
  calc c = c ^ 5 * (c * c)⁻¹ ^ 2 := by group
    _ = 1 := by rw [h5, hc2]; group

section Quotient

variable {Y : Type*} [Group Y]

theorem exists_central_lift (π : M →* Y) (hπ : Function.Surjective π)
    (hZc : ∀ z : M, π z = 1 → ∀ g : M, g * z = z * g) (hZ5 : ∀ z : M, π z = 1 → z ^ 5 = 1)
    {E : Subgroup Y} (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) {nY : Y}
    (hnE : ∀ e ∈ E, nY * e * nY⁻¹ ∈ E) {ℓ : Y} (hℓE : ℓ ∈ E) (hℓinv : nY * ℓ * nY⁻¹ = ℓ⁻¹)
    (hL : ∀ e ∈ E, ∃ k : ℤ, nY * e * nY⁻¹ * e⁻¹ = ℓ ^ k) :
    ∃ ℓ' : M, π ℓ' = ℓ ∧ ∀ y : M, π y ∈ E → ℓ' * y = y * ℓ' := by
  obtain ⟨nM, hnM⟩ := hπ nY
  obtain ⟨ℓM, hℓM⟩ := hπ ℓ
  refine ⟨ℓM, hℓM, fun y hy => ?_⟩
  have hZc' : ∀ z ∈ π.ker, ∀ g : M, g * z = z * g := fun z hz g => hZc z hz g
  have hZ5' : ∀ z ∈ π.ker, z ^ 5 = 1 := fun z hz => hZ5 z hz
  have hu : π (nM * y * nM⁻¹) = nY * π y * nY⁻¹ := by simp [hnM]
  have huE : π (nM * y * nM⁻¹) ∈ E := by rw [hu]; exact hnE _ hy
  have hcomm1 : ∀ a b : Y, a ∈ E → b ∈ E → a * b * a⁻¹ * b⁻¹ = 1 := fun a b ha hb => by
    rw [hEc a ha b hb]
    group
  obtain ⟨k, hk⟩ := hL (π y) hy
  have h1 : nM * ℓM * nM⁻¹ * ℓM ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hnM, hℓM, hℓinv]
    group
  have h2 : ℓM * y * ℓM⁻¹ * y⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hℓM]
    exact hcomm1 _ _ hℓE hy
  have h3 : ℓM * (nM * y * nM⁻¹) * ℓM⁻¹ * (nM * y * nM⁻¹)⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hℓM, hnM] at huE ⊢
    exact hcomm1 _ _ hℓE huE
  have h4 : y * (nM * y * nM⁻¹)⁻¹ * (ℓM ^ (-k))⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, map_zpow, hℓM, hnM]
    have hk' : nY * π y * nY⁻¹ = ℓ ^ k * π y := by rw [← hk]; group
    rw [hk']
    group
  have key := comm_eq_one_of_inverted hZc' hZ5' h1 h2 h3 (-k) h4
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 key)

@[expose] def liftCenter (π : M →* Y) (E : Subgroup Y) : Subgroup Y where
  carrier := {r | r ∈ E ∧ ∃ z : M, π z = r ∧ ∀ y : M, π y ∈ E → z * y = y * z}
  mul_mem' := by
    rintro a b ⟨ha, z₁, hz₁, hc₁⟩ ⟨hb, z₂, hz₂, hc₂⟩
    refine ⟨E.mul_mem ha hb, z₁ * z₂, by rw [map_mul, hz₁, hz₂], fun y hy => ?_⟩
    calc z₁ * z₂ * y = z₁ * (y * z₂) := by rw [mul_assoc, hc₂ y hy]
      _ = (z₁ * y) * z₂ := by rw [mul_assoc]
      _ = (y * z₁) * z₂ := by rw [hc₁ y hy]
      _ = y * (z₁ * z₂) := by rw [mul_assoc]
  one_mem' := ⟨E.one_mem, 1, map_one π, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, z, hz, hc⟩
    refine ⟨E.inv_mem ha, z⁻¹, by rw [map_inv, hz], fun y hy => ?_⟩
    exact (show Commute z y from hc y hy).inv_left.eq

theorem liftCenter_conj (π : M →* Y) (hπ : Function.Surjective π) {E : Subgroup Y} {nY : Y}
    (hn : nY ∈ Subgroup.normalizer (E : Set Y)) {r : Y} (hr : r ∈ liftCenter π E) :
    nY * r * nY⁻¹ ∈ liftCenter π E := by
  obtain ⟨hrE, z, hz, hc⟩ := hr
  obtain ⟨nM, hnM⟩ := hπ nY
  have hn' := Subgroup.mem_normalizer_iff.1 hn
  have hn'' := Subgroup.mem_normalizer_iff.1 (inv_mem hn)
  refine ⟨(hn' r).1 hrE, nM * z * nM⁻¹, by simp [hnM, hz], fun y hy => ?_⟩
  have hy' : π (nM⁻¹ * y * nM) ∈ E := by
    simp only [map_mul, map_inv, hnM]
    have := (hn'' (π y)).1 hy
    simpa using this
  have := hc _ hy'
  calc nM * z * nM⁻¹ * y = nM * (z * (nM⁻¹ * y * nM)) * nM⁻¹ := by group
    _ = nM * ((nM⁻¹ * y * nM) * z) * nM⁻¹ := by rw [this]
    _ = y * (nM * z * nM⁻¹) := by group

theorem comm_of_le_liftCenter (π : M →* Y) (hZc : ∀ z : M, π z = 1 → ∀ g : M, g * z = z * g)
    {E : Subgroup Y} (hle : E ≤ liftCenter π E) {y y' : M} (hy : π y ∈ E) (hy' : π y' ∈ E) :
    y * y' = y' * y := by
  obtain ⟨-, z, hz, hc⟩ := hle hy
  have hker : π (y * z⁻¹) = 1 := by rw [map_mul, map_inv, hz, mul_inv_cancel]
  have e1 := hZc (y * z⁻¹) hker y'
  have e2 := hc y' hy'
  calc y * y' = (y * z⁻¹) * z * y' := by group
    _ = (y * z⁻¹) * (z * y') := mul_assoc _ _ _
    _ = (y * z⁻¹) * (y' * z) := by rw [e2]
    _ = ((y * z⁻¹) * y') * z := (mul_assoc _ _ _).symm
    _ = (y' * (y * z⁻¹)) * z := by rw [e1]
    _ = y' * y := by group

end Quotient

end CFSG.RankThree.PartOne.Q1327C
