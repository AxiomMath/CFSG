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

namespace CFSG.Quasithin.H13.L319.S66

theorem exists_agree_of_mem_iSup {Γ M : Type} [Group Γ] [Group M] [MulAction Γ M]
    (𝓚 : Finset (Subgroup Γ)) (K₀ : Subgroup Γ) (W : Subgroup M)
    (h1 : ∀ K ∈ 𝓚, K ≠ K₀ → ∀ k ∈ K, ∀ w ∈ W, k • w = w)
    (h2 : ∀ k ∈ K₀, ∀ w ∈ W, k • w ∈ W) :
    ∀ g ∈ (⨆ K ∈ 𝓚, K), ∃ k ∈ K₀, ∀ w ∈ W, g • w = k • w := by
  let S : Subgroup Γ :=
    { carrier := {g | ∃ k ∈ K₀, ∀ w ∈ W, g • w = k • w}
      one_mem' := ⟨1, K₀.one_mem, fun _ _ => rfl⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨k₁, hk₁, hg₁⟩ ⟨k₂, hk₂, hg₂⟩
        refine ⟨k₁ * k₂, K₀.mul_mem hk₁ hk₂, fun w hw => ?_⟩
        rw [mul_smul, hg₂ w hw, hg₁ (k₂ • w) (h2 k₂ hk₂ w hw), smul_smul]
      inv_mem' := by
        rintro g ⟨k, hk, hg⟩
        refine ⟨k⁻¹, K₀.inv_mem hk, fun w hw => ?_⟩
        have hw' : k⁻¹ • w ∈ W := h2 k⁻¹ (K₀.inv_mem hk) w hw
        have key : g • (k⁻¹ • w) = w := by
          rw [hg _ hw', smul_inv_smul]
        calc g⁻¹ • w = g⁻¹ • (g • (k⁻¹ • w)) := by rw [key]
          _ = k⁻¹ • w := inv_smul_smul g (k⁻¹ • w) }
  have hle : (⨆ K ∈ 𝓚, K) ≤ S := by
    refine iSup₂_le fun K hK => ?_
    intro g hg
    show ∃ k ∈ K₀, ∀ w ∈ W, g • w = k • w
    by_cases hKK : K = K₀
    · rw [hKK] at hg
      exact ⟨g, hg, fun _ _ => rfl⟩
    · exact ⟨1, K₀.one_mem, fun w hw => by rw [one_smul]; exact h1 K hK hKK g hg w hw⟩
  intro g hg
  exact hle hg

theorem stable_of_mem_iSup {Γ M : Type} [Group Γ] [Group M] [MulAction Γ M]
    (𝓚 : Finset (Subgroup Γ)) (Wk : Subgroup Γ → Subgroup M)
    (hstab : ∀ K ∈ 𝓚, ∀ k ∈ K, ∀ K' ∈ 𝓚, ∀ w : M, k • w ∈ Wk K' ↔ w ∈ Wk K') :
    ∀ g ∈ (⨆ K ∈ 𝓚, K), ∀ K' ∈ 𝓚, ∀ w : M, g • w ∈ Wk K' ↔ w ∈ Wk K' := by
  let S : Subgroup Γ :=
    { carrier := {g | ∀ K' ∈ 𝓚, ∀ w : M, g • w ∈ Wk K' ↔ w ∈ Wk K'}
      one_mem' := by
        intro K' _ w
        rw [one_smul]
      mul_mem' := by
        intro g₁ g₂ h₁ h₂ K' hK' w
        rw [mul_smul]
        exact (h₁ K' hK' (g₂ • w)).trans (h₂ K' hK' w)
      inv_mem' := by
        intro g hg K' hK' w
        have h := hg K' hK' (g⁻¹ • w)
        rw [smul_inv_smul] at h
        exact h.symm }
  have hle : (⨆ K ∈ 𝓚, K) ≤ S := by
    refine iSup₂_le fun K hK => ?_
    intro k hk K' hK' w
    exact hstab K hK k hk K' hK' w
  intro g hg
  exact hle hg

end CFSG.Quasithin.H13.L319.S66

end
