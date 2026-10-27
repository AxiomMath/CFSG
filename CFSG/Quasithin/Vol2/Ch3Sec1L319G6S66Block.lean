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

theorem ncard_coboundary_le_four_of_blocks {M : Type} [CommGroup M] [Finite M] {β : Type} [DecidableEq β]
    (𝓚 : Finset β) (Wk : β → Subgroup M) (K₀ : β) (hK₀ : K₀ ∈ 𝓚)
    (hsum : (⨆ K ∈ 𝓚, Wk K) = ⊤)
    (hdir : Wk K₀ ⊓ (⨆ K ∈ 𝓚, ⨆ (_ : K ≠ K₀), Wk K) = ⊥)
    (σ : M →* M) (hσ : ∀ K ∈ 𝓚, K ≠ K₀ → ∀ w ∈ Wk K, σ w = w)
    (e : M →* M) (he : ∀ K ∈ 𝓚, ∀ w ∈ Wk K, e w ∈ Wk K)
    (Vs : Subgroup M) (hVs : ∀ v ∈ Vs, e v = v)
    (hfix : Set.ncard {w : M | w ∈ Wk K₀ ∧ e w = w} ≤ 4) :
    Set.ncard ((fun v => σ v * v⁻¹) '' (Vs : Set M)) ≤ 4 := by
  classical
  set R : Subgroup M := ⨆ K ∈ 𝓚, ⨆ (_ : K ≠ K₀), Wk K with hRdef
  have hWR : ∀ K ∈ 𝓚, K ≠ K₀ → Wk K ≤ R := fun K hK hne =>
    le_iSup_of_le K (le_iSup_of_le hK (le_iSup_of_le hne le_rfl))
  have hsplit : Wk K₀ ⊔ R = ⊤ := by
    rw [← hsum]
    refine le_antisymm (sup_le ?_ ?_) ?_
    · exact le_iSup_of_le K₀ (le_iSup_of_le hK₀ le_rfl)
    · exact iSup₂_le fun K hK => iSup_le fun hne => le_iSup_of_le K (le_iSup_of_le hK le_rfl)
    · refine iSup₂_le fun K hK => ?_
      by_cases h : K = K₀
      · subst h
        exact le_sup_left
      · exact le_sup_of_le_right (hWR K hK h)
  have hdec : ∀ v : M, ∃ w ∈ Wk K₀, ∃ r ∈ R, w * r = v := by
    intro v
    have hv : v ∈ Wk K₀ ⊔ R := by
      rw [hsplit]
      exact Subgroup.mem_top v
    exact Subgroup.mem_sup.mp hv
  have hRe : ∀ r ∈ R, e r ∈ R := by
    have hle : R ≤ R.comap e := by
      refine iSup₂_le fun K hK => iSup_le fun hne => ?_
      intro x hx
      exact hWR K hK hne (he K hK x hx)
    exact fun r hr => hle hr
  let Fx : Subgroup M :=
    { carrier := {x | σ x = x}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hRσ : ∀ r ∈ R, σ r = r := by
    have hle : R ≤ Fx := by
      refine iSup₂_le fun K hK => iSup_le fun hne => ?_
      intro x hx
      exact hσ K hK hne x hx
    exact fun r hr => hle hr
  have hsub : (fun v => σ v * v⁻¹) '' (Vs : Set M) ⊆
      (fun w => σ w * w⁻¹) '' {w : M | w ∈ Wk K₀ ∧ e w = w} := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, r, hr, hwr⟩ := hdec v
    have hev : e v = v := hVs v hv
    have h1 : e w * e r = w * r := by
      rw [← map_mul, hwr, hev]
    have h2 : e w = w * r * (e r)⁻¹ := eq_mul_inv_of_mul_eq h1
    have hmem1 : e w * w⁻¹ ∈ Wk K₀ :=
      Wk K₀ |>.mul_mem (he K₀ hK₀ w hw) (Wk K₀ |>.inv_mem hw)
    have hmem2 : e w * w⁻¹ ∈ R := by
      have : e w * w⁻¹ = r * (e r)⁻¹ := by
        calc e w * w⁻¹ = (w * w⁻¹) * (r * (e r)⁻¹) := by rw [h2]; ac_rfl
          _ = r * (e r)⁻¹ := by rw [mul_inv_cancel, one_mul]
      rw [this]
      exact R.mul_mem hr (R.inv_mem (hRe r hr))
    have h0 : e w * w⁻¹ = 1 := by
      have : e w * w⁻¹ ∈ Wk K₀ ⊓ R := Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
      rw [hdir, Subgroup.mem_bot] at this
      exact this
    have hew : e w = w := mul_inv_eq_one.mp h0
    refine ⟨w, ⟨hw, hew⟩, ?_⟩
    have hσv : σ v = σ w * r := by
      rw [← hwr]
      simp only [map_mul, hRσ r hr]
    show σ w * w⁻¹ = σ v * v⁻¹
    rw [hσv, ← hwr, mul_inv]
    calc σ w * w⁻¹ = (σ w * w⁻¹) * (r * r⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = σ w * r * (w⁻¹ * r⁻¹) := by ac_rfl
  calc Set.ncard ((fun v => σ v * v⁻¹) '' (Vs : Set M))
      ≤ Set.ncard ((fun w => σ w * w⁻¹) '' {w : M | w ∈ Wk K₀ ∧ e w = w}) :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Set.ncard {w : M | w ∈ Wk K₀ ∧ e w = w} := Set.ncard_image_le (Set.toFinite _)
    _ ≤ 4 := hfix

end CFSG.Quasithin.H13.L319.S66

end
