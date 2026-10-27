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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

open Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {X : Type} [Group X]

@[expose] def vecStab (ρ : X →* GL ι K) (w₀ : ι → K) : Subgroup X where
  carrier := {g | ((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w₀ = w₀}
  mul_mem' {a b} ha hb := by
    change ((ρ (a * b) : GL ι K) : Matrix ι ι K) *ᵥ w₀ = w₀
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb, ha]
  one_mem' := by
    change ((ρ (1 : X) : GL ι K) : Matrix ι ι K) *ᵥ w₀ = w₀
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  inv_mem' {a} ha := by
    change ((ρ (a⁻¹) : GL ι K) : Matrix ι ι K) *ᵥ w₀ = w₀
    have h := congrArg (fun v => ((ρ (a⁻¹) : GL ι K) : Matrix ι ι K) *ᵥ v) ha
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec] at h
    exact h.symm

@[simp]
theorem mem_vecStab {ρ : X →* GL ι K} {w₀ : ι → K} {g : X} :
    g ∈ vecStab ρ w₀ ↔ ((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w₀ = w₀ :=
  Iff.rfl

theorem exists_lineChar (ρ : X →* GL ι K) {w₀ : ι → K} (hw₀ : w₀ ≠ 0) {B : Subgroup X}
    (hB : ∀ g ∈ B, ∃ c : K, ((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w₀ = c • w₀) :
    ∃ χ : ↥B →* Kˣ, (∀ g : ↥B, ((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w₀ = (χ g : K) • w₀) ∧
      χ.ker = (B ⊓ vecStab ρ w₀).subgroupOf B := by
  classical
  let c : ↥B → K := fun g => Classical.choose (hB (g : X) g.2)
  have hc : ∀ g : ↥B, ((ρ (g : X) : GL ι K) : Matrix ι ι K) *ᵥ w₀ = c g • w₀ :=
    fun g => Classical.choose_spec (hB (g : X) g.2)
  have hc_ne : ∀ g : ↥B, c g ≠ 0 := by
    intro g hg
    have h : ((ρ (g : X) : GL ι K) : Matrix ι ι K) *ᵥ w₀ = 0 := by
      rw [hc g, hg, zero_smul]
    have h' := congrArg (fun v => ((ρ (g : X)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) h
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec, Matrix.mulVec_zero] at h'
    exact hw₀ h'
  have hsmul : ∀ g h : ↥B, c (g * h) = c g * c h := by
    intro g h
    refine smul_left_injective K hw₀ ?_
    change c (g * h) • w₀ = (c g * c h) • w₀
    rw [← hc (g * h), Subgroup.coe_mul, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      hc h, Matrix.mulVec_smul, hc g, smul_smul, mul_comm (c h) (c g)]
  let χ : ↥B →* Kˣ := MonoidHom.mk' (fun g : ↥B => Units.mk0 (c g) (hc_ne g))
    (fun g h => by
      ext
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]
      exact hsmul g h)
  refine ⟨χ, ?_, ?_⟩
  · intro g
    exact hc g
  · ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_vecStab]
    constructor
    · intro h
      refine ⟨g.2, ?_⟩
      have hval : c g = 1 := by
        have h' := congrArg (fun u : Kˣ => (u : K)) h
        rw [Units.val_one] at h'
        exact h'
      rw [hc g, hval, one_smul]
    · intro h
      apply Units.ext
      have hc1 : c g = 1 := by
        apply smul_left_injective K hw₀
        change c g • w₀ = 1 • w₀
        rw [← hc g, h.2, one_smul]
      show (χ g : K) = 1
      rw [show (χ g : K) = c g from rfl, hc1]

theorem index_vecStab_dvd [Finite K] (ρ : X →* GL ι K) {w₀ : ι → K} (hw₀ : w₀ ≠ 0)
    {B : Subgroup X} (hB : ∀ g ∈ B, ∃ c : K, ((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w₀ = c • w₀) :
    ((B ⊓ vecStab ρ w₀).subgroupOf B).index ∣ Nat.card K - 1 := by
  obtain ⟨χ, -, hker⟩ := exists_lineChar ρ hw₀ hB
  rw [← hker, Subgroup.index_ker]
  have h := Subgroup.card_subgroup_dvd_card χ.range
  rwa [Nat.card_units] at h

theorem isCyclic_of_inf_vecStab_eq_bot [Finite K] (ρ : X →* GL ι K) {w₀ : ι → K}
    (hw₀ : w₀ ≠ 0) {B : Subgroup X}
    (hB : ∀ g ∈ B, ∃ c : K, ((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w₀ = c • w₀) {E : Subgroup X}
    (hEB : E ≤ B) (hE : E ⊓ vecStab ρ w₀ = ⊥) : IsCyclic ↥E := by
  obtain ⟨χ, -, hker⟩ := exists_lineChar ρ hw₀ hB
  let f : ↥E →* K := (Units.coeHom K).comp (χ.comp (Subgroup.inclusion hEB))
  have hfker : f.ker = ⊥ := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h
      have hχ : χ (Subgroup.inclusion hEB g) = 1 := by
        apply Units.ext
        simpa [f] using h
      have hmem : Subgroup.inclusion hEB g ∈ χ.ker := hχ
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hmem
      have hbot : (g : X) ∈ (⊥ : Subgroup X) := by
        rw [← hE]
        exact ⟨g.2, hmem.2⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hbot)
    · intro h
      rw [h, map_one]
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hfker
  haveI : Finite ↥E := Finite.of_injective f hf
  exact isCyclic_of_subgroup_isDomain f hf

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

end
