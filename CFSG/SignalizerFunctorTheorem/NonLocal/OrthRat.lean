module

public import CFSG.ClassicalGroups.Orthogonal.Perfect
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal.Orth

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem span_singular_eq_top (P : HypPair Q) :
    Submodule.span K {u : V | Q u = 0} = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have he : P.e ∈ Submodule.span K {u : V | Q u = 0} := Submodule.subset_span P.Q_e
  have hf : P.f ∈ Submodule.span K {u : V | Q u = 0} := Submodule.subset_span P.Q_f
  have hz := P.proj_mem_perp v
  rw [HypPair.mem_perp] at hz
  set z := P.proj v with hzdef
  have hsing : Q (z + P.e - Q z • P.f) = 0 := by
    have h1 : z + P.e - Q z • P.f = (z + P.e) + (-Q z) • P.f := by
      rw [sub_eq_add_neg, neg_smul]
    rw [h1, QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, P.Q_e, P.Q_f]
    simp only [polar_add_left, polar_smul_right_eq, polar_comm Q z P.e, polar_comm Q z P.f,
      hz.1, hz.2, P.polar_ef]
    ring
  have hz' : z ∈ Submodule.span K {u : V | Q u = 0} := by
    have h1 : z = (z + P.e - Q z • P.f) - P.e + Q z • P.f := by abel
    rw [h1]
    exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.subset_span hsing) he)
      (Submodule.smul_mem _ _ hf)
  rw [P.eq_add_proj v]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ he)
    (Submodule.smul_mem _ _ hf)) hz'

theorem exchange_mem (Pa Pb : HypPair Q) (h : Pa.Orth Pb) (W : Submodule K V)
    (hW1 : ∀ x ∈ W, eichler Q Pa.e Pb.e x ∈ W) (hW2 : ∀ x ∈ W, eichler Q Pa.e Pb.f x ∈ W)
    {x : V} (hx : x ∈ W) (ha : polar Q x Pa.e ≠ 0) : Pa.e ∈ W := by
  set a := polar Q x Pa.e with ha_def
  set c := polar Q x Pb.e with hc_def
  have hz1 : eichler Q Pa.e Pb.e x - x = a • Pb.e - c • Pa.e := by
    rw [eichler_apply Pa.Q_e h.ee, Pb.Q_e]
    simp only [zero_mul, add_zero]
    module
  set z₁ := a • Pb.e - c • Pa.e with hz₁
  have hz₁W : z₁ ∈ W := by rw [← hz1]; exact W.sub_mem (hW1 x hx) hx
  have hpe : polar Q z₁ Pa.e = 0 := by
    rw [hz₁, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, polar_comm Q Pb.e Pa.e,
      h.ee, Pa.polar_ee]
    ring
  have hpf : polar Q z₁ Pb.f = a := by
    rw [hz₁, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, Pb.polar_ef, h.ef]
    ring
  have hz2 : eichler Q Pa.e Pb.f z₁ - z₁ = (-a) • Pa.e := by
    rw [eichler_apply Pa.Q_e h.ef, Pb.Q_f, hpe, hpf]
    simp only [zero_smul, mul_zero, add_zero]
    module
  have hz₂W : (-a) • Pa.e ∈ W := by rw [← hz2]; exact W.sub_mem (hW2 z₁ hz₁W) hz₁W
  have := W.smul_mem (-a)⁻¹ hz₂W
  rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr ha), one_smul] at this

theorem perp_extract_mem (Pa : HypPair Q) (W : Submodule K V) {x : V} (hx : x ∈ W)
    (hxa : polar Q x Pa.e = 0) {w : V} (hw : w ∈ Pa.perp) (hE : eichler Q Pa.e w x ∈ W)
    (hxw : polar Q x w ≠ 0) : Pa.e ∈ W := by
  have hwe : polar Q Pa.e w = 0 := (HypPair.mem_perp.mp hw).1
  have h1 : eichler Q Pa.e w x - x = (-polar Q x w) • Pa.e := by
    rw [eichler_apply Pa.Q_e hwe, hxa]
    simp only [zero_smul, mul_zero, add_zero]
    module
  have h2 : (-polar Q x w) • Pa.e ∈ W := by rw [← h1]; exact W.sub_mem hE hx
  have := W.smul_mem (-polar Q x w)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hxw), one_smul] at this

@[expose] def swapPair (P : HypPair Q) : HypPair Q where
  e := P.f
  f := P.e
  Q_e := P.Q_f
  Q_f := P.Q_e
  polar_ef := P.polar_fe

theorem orth_swapPair_left {P P' : HypPair Q} (h : P.Orth P') : (swapPair P).Orth P' where
  ee := h.fe
  ef := h.ff
  fe := h.ee
  ff := h.ef

theorem commutator_eichler_heis {e₁ e₂ w w' : V} (he₂ : Q e₂ = 0) (h12 : polar Q e₁ e₂ = 0)
    (hw₁ : polar Q e₁ w = 0) (hw₂ : polar Q e₂ w = 0) (hw'₁ : polar Q e₁ w' = 0)
    (hw'₂ : polar Q e₂ w' = 0) :
    ⁅(eichler Q e₂ w')⁻¹, eichler Q e₁ w⁆ = eichler Q e₁ (polar Q w w' • e₂) := by
  rw [eichler_inv hw'₂]
  have hneg : polar Q e₂ (-w') = 0 := by rw [polar_neg_right, hw'₂, neg_zero]
  have hg : eichler Q e₂ (-w') ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    eichler_mem_orthogonalGroup Q _ _
  have hge₁ : eichler Q e₂ (-w') e₁ = e₁ := by
    apply eichler_apply_of_polar_eq_zero
    · exact h12
    · rw [polar_neg_right, hw'₁, neg_zero]
  rw [commutatorElement_eichler hg hge₁ hw₁]
  congr 1
  rw [eichler_apply he₂ hneg, polar_comm Q w e₂, hw₂, polar_neg_right, QuadraticMap.map_neg]
  simp only [zero_smul, mul_zero, add_zero]
  module

end Abstract

section Perp

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {Q : QuadraticForm k V}

theorem finrank_perp2_ge [FiniteDimensional k V] (P₁ P₂ : HypPair Q) :
    Module.finrank k V ≤ Module.finrank k ↥(P₁.perp ⊓ P₂.perp) + 4 := by
  let φ : V →ₗ[k] (Fin 4 → k) :=
    LinearMap.pi ![polarBilin Q P₁.e, polarBilin Q P₁.f, polarBilin Q P₂.e, polarBilin Q P₂.f]
  have hker : LinearMap.ker φ = P₁.perp ⊓ P₂.perp := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_inf, HypPair.mem_perp, funext_iff,
      Fin.forall_fin_succ, φ]
    simp [LinearMap.pi_apply, polarBilin_apply_apply]
    tauto
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : Module.finrank k (LinearMap.range φ) ≤ 4 := by
    calc Module.finrank k (LinearMap.range φ) ≤ Module.finrank k (Fin 4 → k) :=
          Submodule.finrank_le _
      _ = 4 := by simp
  rw [hker] at h1
  omega

theorem exists_dual_perp [FiniteDimensional k V] (hQ : (polarBilin Q).Nondegenerate)
    (P₁ P₂ : HypPair Q) (h : P₁.Orth P₂) {n : ℕ} {t : Fin n → V} (ht : LinearIndependent k t)
    (htP : ∀ i, t i ∈ P₁.perp ⊓ P₂.perp) :
    ∃ g : Fin n → V, (∀ j, polar Q P₁.e (g j) = 0 ∧ polar Q P₂.e (g j) = 0) ∧
      ∀ i j, polar Q (t i) (g j) = if i = j then 1 else 0 := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ ht
  refine ⟨fun j => g j - polar Q (g j) P₁.e • P₁.f - polar Q (g j) P₂.e • P₂.f, fun j => ?_,
    fun i j => ?_⟩
  · have h12 : polar Q P₁.e P₂.f = 0 := h.ef
    have h21 : polar Q P₂.e P₁.f = 0 := h.symm.ef
    constructor
    · simp only [polar_sub_right, polar_smul_right_eq, P₁.polar_ef, h12, polar_comm Q P₁.e (g j)]
      ring
    · simp only [polar_sub_right, polar_smul_right_eq, P₂.polar_ef, h21, polar_comm Q P₂.e (g j)]
      ring
  · have hti := Submodule.mem_inf.mp (htP i)
    have hf₁ : polar Q (t i) P₁.f = 0 := by
      rw [polar_comm]; exact (HypPair.mem_perp.mp hti.1).2
    have hf₂ : polar Q (t i) P₂.f = 0 := by
      rw [polar_comm]; exact (HypPair.mem_perp.mp hti.2).2
    simp only [polar_sub_right, polar_smul_right_eq, hf₁, hf₂, mul_zero, sub_zero]
    exact hg i j

end Perp

end CFSG.SignalizerFunctorTheorem.NonLocal.Orth
