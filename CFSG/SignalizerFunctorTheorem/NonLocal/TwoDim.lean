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

public section

open Module Module.End Matrix
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem eq_one_or_neg_one_of_sq {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (T : Module.End F (Fin 2 → F)) (hT : T * T = 1) (hdet : LinearMap.det T = 1) :
    T = 1 ∨ T = -1 := by
  set M : Matrix (Fin 2) (Fin 2) F := LinearMap.toMatrix' T with hM
  have hMM : M * M = 1 := by
    have := congrArg LinearMap.toMatrix' hT
    rw [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_one] at this
    exact this
  have hdetM : M.det = 1 := by rw [hM, LinearMap.det_toMatrix', hdet]
  rw [Matrix.det_fin_two] at hdetM
  have e00 := congrFun (congrFun hMM 0) 0
  have e01 := congrFun (congrFun hMM 0) 1
  have e10 := congrFun (congrFun hMM 1) 0
  have e11 := congrFun (congrFun hMM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hsum : M 0 0 + M 1 1 ≠ 0 := by
    intro h
    have h3 : M 0 0 * (M 0 0 + M 1 1) = 2 := by linear_combination e00 + hdetM
    rw [h, mul_zero] at h3
    exact h2 h3.symm
  have hb : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hsum
  have hc : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hsum
  rw [hb, hc] at e00 e11 hdetM
  have ha1 : M 0 0 * M 0 0 = 1 := by simpa using e00
  have hd1 : M 1 1 * M 1 1 = 1 := by simpa using e11
  have had : M 0 0 * M 1 1 = 1 := by simpa using hdetM
  have ha0 : M 0 0 ≠ 0 := by
    intro h
    rw [h] at ha1
    simp at ha1
  have hda : M 1 1 = M 0 0 := by
    have : M 0 0 * (M 1 1 - M 0 0) = 0 := by linear_combination had - ha1
    have := (mul_eq_zero.mp this).resolve_left ha0
    exact sub_eq_zero.mp this
  have hcases : M 0 0 = 1 ∨ M 0 0 = -1 := by
    have : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination ha1
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hMdiag : ∀ a : F, M 0 0 = a → M = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro a h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hda, h]
  rcases hcases with h | h
  · left
    apply LinearMap.toMatrix'.injective
    rw [LinearMap.toMatrix'_one]
    have := hMdiag 1 h
    rwa [one_smul] at this
  · right
    apply LinearMap.toMatrix'.injective
    have := hMdiag (-1) h
    rw [neg_smul, one_smul] at this
    rw [map_neg, LinearMap.toMatrix'_one]
    exact this

theorem not_faithful_dim_two {F C : Type*} [Field F] [Group C] [IsSimpleGroup C]
    (hnonab : ∃ a b : C, a * b ≠ b * a) (h2 : (2 : F) ≠ 0)
    (ρ : C →* Module.End F (Fin 2 → F)) (hρ : Function.Injective ρ) (u₁ u₂ : C)
    (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1) (h1 : u₁ ≠ 1) (h1' : u₂ ≠ 1) (hne : u₁ ≠ u₂) :
    False := by
  let dρ : C →* F := (LinearMap.det : Module.End F (Fin 2 → F) →* F).comp ρ
  let δ : C →* Fˣ := dρ.toHomUnits
  have hdet : ∀ c : C, LinearMap.det (ρ c) = 1 := by
    have : δ.ker = ⊥ ∨ δ.ker = ⊤ := IsSimpleGroup.eq_bot_or_eq_top_of_normal δ.ker
    rcases this with hbot | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have hδ : Function.Injective δ := (MonoidHom.ker_eq_bot_iff δ).mp hbot
      apply hδ
      rw [map_mul, map_mul, mul_comm]
    · intro c
      have hc : c ∈ δ.ker := by rw [htop]; exact Subgroup.mem_top c
      have : δ c = 1 := hc
      have h3 : ((δ c : Fˣ) : F) = 1 := by rw [this]; rfl
      simpa [δ, dρ] using h3
  have key : ∀ u : C, u ^ 2 = 1 → u ≠ 1 → ρ u = -1 := by
    intro u hu hne1
    have hT : ρ u * ρ u = 1 := by
      rw [← map_mul, ← pow_two, hu, map_one]
    rcases eq_one_or_neg_one_of_sq h2 _ hT (hdet u) with h | h
    · exact absurd (hρ (h.trans (map_one ρ).symm)) hne1
    · exact h
  exact hne (hρ ((key u₁ hu₁ h1).trans (key u₂ hu₂ h1').symm))

end CFSG.SignalizerFunctorTheorem.NonLocal
