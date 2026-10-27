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

namespace CFSG.RankThree.PartOne.KCGeneric

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {τ : K →+* K}

theorem semilinear_ne_zero_of_injective (γ : V →ₛₗ[τ] V) (hγ : Function.Injective γ) {e : V}
    (he : e ≠ 0) : γ e ≠ 0 := fun h0 => he (hγ (by rw [h0, map_zero]))

theorem semilinear_eigenvector_of_torus_single (γ : V →ₛₗ[τ] V) (hγ : Function.Injective γ)
    {e : V} (he : e ≠ 0) (Y : V →ₗ[K] V) {c : K}
    (hrange : ∀ v, Y v - v ∈ Submodule.span K {e}) (hYe : Y e = c • e) (hc : τ c ≠ 1)
    (hcomm : ∀ v, γ (Y v) = Y (γ v)) :
    (∃ d : K, d ≠ 0 ∧ γ e = d • e) ∧ τ c = c := by
  have hu0 : γ e ≠ 0 := semilinear_ne_zero_of_injective γ hγ he
  have hYu : Y (γ e) = τ c • γ e := by
    rw [← hcomm, hYe, map_smulₛₗ]
  have h1 : Y (γ e) - γ e = (τ c - 1) • γ e := by rw [hYu, sub_smul, one_smul]
  have hsub : τ c - 1 ≠ 0 := sub_ne_zero.mpr hc
  have h2 : γ e ∈ Submodule.span K {e} := by
    have h3 := hrange (γ e)
    rw [h1] at h3
    have := Submodule.smul_mem _ (τ c - 1)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hsub, one_smul] at this
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp h2
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hd
    exact hu0 hd.symm
  refine ⟨⟨d, hd0, hd.symm⟩, ?_⟩
  have h4 : Y (γ e) = (d * c) • e := by
    rw [← hd, map_smul, hYe, smul_smul]
  have h5 : τ c • γ e = (τ c * d) • e := by rw [← hd, smul_smul]
  rw [hYu, h5, mul_comm d c] at h4
  have h6 : (c * d - τ c * d) • e = 0 := by rw [sub_smul, h4, sub_self]
  have h7 := (smul_eq_zero.mp h6).resolve_right he
  have h8 : (c - τ c) * d = 0 := by linear_combination h7
  exact ((mul_eq_zero.mp h8).resolve_right hd0 |> sub_eq_zero.mp).symm

theorem semilinear_eigenvector_of_torus_pair (γ : V →ₛₗ[τ] V) (hγ : Function.Injective γ)
    {e₁ e₂ : V} (hind : LinearIndependent K ![e₁, e₂]) (Y : V →ₗ[K] V) {c c' : K}
    (hrange : ∀ v, Y v - v ∈ Submodule.span K {e₁, e₂}) (h₁ : Y e₁ = c • e₁)
    (h₂ : Y e₂ = c' • e₂) (hcc : c ≠ c') (hc : τ c ≠ 1) (hcomm : ∀ v, γ (Y v) = Y (γ v)) :
    ((∃ d : K, d ≠ 0 ∧ γ e₁ = d • e₁) ∧ τ c = c) ∨
      ((∃ d : K, d ≠ 0 ∧ γ e₁ = d • e₂) ∧ τ c = c') := by
  have he₁ : e₁ ≠ 0 := by
    intro h0
    have := LinearIndependent.ne_zero 0 hind
    exact this h0
  have hu0 : γ e₁ ≠ 0 := semilinear_ne_zero_of_injective γ hγ he₁
  have hYu : Y (γ e₁) = τ c • γ e₁ := by
    rw [← hcomm, h₁, map_smulₛₗ]
  have h1 : Y (γ e₁) - γ e₁ = (τ c - 1) • γ e₁ := by rw [hYu, sub_smul, one_smul]
  have hsub : τ c - 1 ≠ 0 := sub_ne_zero.mpr hc
  have h2 : γ e₁ ∈ Submodule.span K {e₁, e₂} := by
    have h3 := hrange (γ e₁)
    rw [h1] at h3
    have := Submodule.smul_mem _ (τ c - 1)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hsub, one_smul] at this
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h2
  have h4 : Y (γ e₁) = (α * c) • e₁ + (β * c') • e₂ := by
    rw [← hαβ, map_add, map_smul, map_smul, h₁, h₂, smul_smul, smul_smul]
  have h5 : τ c • γ e₁ = (τ c * α) • e₁ + (τ c * β) • e₂ := by
    rw [← hαβ, smul_add, smul_smul, smul_smul]
  rw [hYu, h5] at h4
  have h6 : (τ c * α - α * c) • e₁ + (τ c * β - β * c') • e₂ = 0 := by
    calc (τ c * α - α * c) • e₁ + (τ c * β - β * c') • e₂
        = ((τ c * α) • e₁ + (τ c * β) • e₂) - ((α * c) • e₁ + (β * c') • e₂) := by
          simp only [sub_smul]
          abel
      _ = 0 := sub_eq_zero.mpr h4
  obtain ⟨hs, ht⟩ := LinearIndependent.pair_iff.mp hind _ _ h6
  by_cases hα : α = 0
  · right
    subst hα
    have hβ : β ≠ 0 := by
      rintro rfl
      simp only [zero_smul, add_zero] at hαβ
      exact hu0 hαβ.symm
    refine ⟨⟨β, hβ, ?_⟩, ?_⟩
    · rw [← hαβ, zero_smul, zero_add]
    · have h7 : β * (τ c - c') = 0 := by linear_combination ht
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7).resolve_left hβ)
  · left
    have h7 : α * (τ c - c) = 0 := by linear_combination hs
    have hτ : τ c = c := sub_eq_zero.mp ((mul_eq_zero.mp h7).resolve_left hα)
    refine ⟨⟨α, hα, ?_⟩, hτ⟩
    have h8 : β * (c - c') = 0 := by rw [hτ] at ht; linear_combination ht
    have hβ : β = 0 := (mul_eq_zero.mp h8).resolve_right (sub_ne_zero.mpr hcc)
    rw [← hαβ, hβ, zero_smul, add_zero]

theorem semilinear_fixes_of_torus_triple (γ : V →ₛₗ[τ] V) (hγ : Function.Injective γ)
    {e₁ e₂ e₃ : V} (hind : LinearIndependent K ![e₁, e₂, e₃]) (Y₂ Y₃ : V →ₗ[K] V)
    {c c₂ c₃ : K} (hr₂ : ∀ v, Y₂ v - v ∈ Submodule.span K {e₁, e₂})
    (hr₃ : ∀ v, Y₃ v - v ∈ Submodule.span K {e₁, e₃}) (h₁₂ : Y₂ e₁ = c • e₁)
    (h₂ : Y₂ e₂ = c₂ • e₂) (h₁₃ : Y₃ e₁ = c • e₁) (h₃ : Y₃ e₃ = c₃ • e₃) (hc₂ : c ≠ c₂)
    (hc₃ : c ≠ c₃) (hc : τ c ≠ 1) (hcomm₂ : ∀ v, γ (Y₂ v) = Y₂ (γ v))
    (hcomm₃ : ∀ v, γ (Y₃ v) = Y₃ (γ v)) : τ c = c := by
  have hind12 : LinearIndependent K ![e₁, e₂] := by
    have := hind.comp ![0, 1] (by decide)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  have hind13 : LinearIndependent K ![e₁, e₃] := by
    have := hind.comp ![0, 2] (by decide)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  have hind3 : ∀ s t u : K, s • e₁ + t • e₂ + u • e₃ = 0 → s = 0 ∧ t = 0 ∧ u = 0 := by
    intro s t u hstu
    have := Fintype.linearIndependent_iff.mp hind ![s, t, u] (by
      simpa [Fin.sum_univ_succ, add_assoc] using hstu)
    exact ⟨this 0, this 1, this 2⟩
  rcases semilinear_eigenvector_of_torus_pair γ hγ hind12 Y₂ hr₂ h₁₂ h₂ hc₂ hc hcomm₂ with
    ⟨_, h⟩ | ⟨⟨d, hd, hγe⟩, _⟩
  · exact h
  · exfalso
    rcases semilinear_eigenvector_of_torus_pair γ hγ hind13 Y₃ hr₃ h₁₃ h₃ hc₃ hc hcomm₃ with
      ⟨⟨d', hd', hγe'⟩, _⟩ | ⟨⟨d', hd', hγe'⟩, _⟩
    · have h0 : (-d') • e₁ + d • e₂ + (0 : K) • e₃ = 0 := by
        rw [neg_smul, zero_smul, add_zero, ← hγe', hγe]
        exact neg_add_cancel _
      exact hd (hind3 _ _ _ h0).2.1
    · have h0 : (0 : K) • e₁ + d • e₂ + (-d') • e₃ = 0 := by
        rw [neg_smul, zero_smul, zero_add, ← sub_eq_add_neg, sub_eq_zero, ← hγe', hγe]
      exact hd (hind3 _ _ _ h0).2.1

end CFSG.RankThree.PartOne.KCGeneric
