module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.FixedLine
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open scoped Matrix Pointwise

private lemma fs_coe_mulAut_conj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (GL ι K)} (g t : ↥Γ) :
    (((MulAut.conj g) t : ↥Γ) : GL ι K) = MulAut.conj (g : GL ι K) (t : GL ι K) :=
  rfl

private lemma fs_conj_mulVec_fixed {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {γ τ : GL ι K} {v : ι → K}
    (hv : ((τ : GL ι K) : Matrix ι ι K) *ᵥ v = v) :
    ((((MulAut.conj γ τ : GL ι K)) : Matrix ι ι K)) *ᵥ
        (((γ : GL ι K) : Matrix ι ι K) *ᵥ v) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ v := by
  have hCγ : (((γ⁻¹ : GL ι K)) : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel]
    rfl
  calc ((((MulAut.conj γ τ : GL ι K)) : Matrix ι ι K)) *ᵥ
          (((γ : GL ι K) : Matrix ι ι K) *ᵥ v)
      = ((((MulAut.conj γ τ : GL ι K)) : Matrix ι ι K) *
            ((γ : GL ι K) : Matrix ι ι K)) *ᵥ v := Matrix.mulVec_mulVec v _ _
    _ = ((((γ : GL ι K) : Matrix ι ι K) * ((τ : GL ι K) : Matrix ι ι K)) *
            (((γ⁻¹ : GL ι K)) : Matrix ι ι K) *
              ((γ : GL ι K) : Matrix ι ι K)) *ᵥ v := by
          rw [MulAut.conj_apply, Units.val_mul, Units.val_mul]
    _ = (((γ : GL ι K) : Matrix ι ι K) * ((τ : GL ι K) : Matrix ι ι K)) *ᵥ v := by
          rw [mul_assoc, hCγ, mul_one]
    _ = ((γ : GL ι K) : Matrix ι ι K) *ᵥ
          (((τ : GL ι K) : Matrix ι ι K) *ᵥ v) :=
          (Matrix.mulVec_mulVec v _ _).symm
    _ = ((γ : GL ι K) : Matrix ι ι K) *ᵥ v := by rw [hv]

private lemma fs_mulVec_inv_mulVec {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (g : GL ι K) (v : ι → K) :
    (((g : GL ι K) : Matrix ι ι K) * (((g⁻¹ : GL ι K) : Matrix ι ι K))) *ᵥ v = v := by
  have h : ((g : GL ι K) : Matrix ι ι K) * (((g⁻¹ : GL ι K) : Matrix ι ι K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]
    rfl
  rw [h, Matrix.one_mulVec]

private lemma fs_smul_mem_fixed_conj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (GL ι K)} (g : ↥Γ) (T : Subgroup ↥Γ) {v : ι → K}
    (hv : ∀ t ∈ T, ((t : GL ι K) : Matrix ι ι K) *ᵥ v = v) :
    ∀ s ∈ (MulAut.conj g • T : Subgroup ↥Γ),
      ((s : GL ι K) : Matrix ι ι K) *ᵥ ((((g : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v =
        ((((g : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists s (MulAut.conj g) T).mp hs
  change (((MulAut.conj g t : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ
        ((((g : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v =
      ((((g : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v
  rw [fs_coe_mulAut_conj]
  exact fs_conj_mulVec_fixed (γ := (g : GL ι K)) (τ := (t : GL ι K)) (hv t ht)

private lemma fs_mem_span_conj_of_fixed {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (GL ι K)} (U P S : Subgroup ↥Γ) (hUP : U ≤ P) (e : ι → K)
    (hfix : ∀ v : ι → K,
      (∀ u ∈ U, ((u : GL ι K) : Matrix ι ι K) *ᵥ v = v) → v ∈ Submodule.span K {e})
    (g : ↥Γ) (hgS : S = MulAut.conj g • P) {v : ι → K}
    (hv : ∀ s ∈ S, ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v) :
    v ∈ Submodule.span K {(((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e} := by
  have hconjP : MulAut.conj (g⁻¹) • S = P := by
    rw [hgS, map_inv (MulAut.conj) g, inv_smul_smul]
  have hPfix := fs_smul_mem_fixed_conj (g⁻¹) S hv
  rw [hconjP] at hPfix
  have hspan : ((((g⁻¹ : ↥Γ) : GL ι K)) : Matrix ι ι K) *ᵥ v ∈ Submodule.span K {e} :=
    hfix _ (fun u hu => hPfix u (hUP hu))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  calc c • ((((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e)
      = (((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ (c • e) :=
        (Matrix.mulVec_smul _ c e).symm
    _ = ((((g : ↥Γ) : GL ι K) : Matrix ι ι K) *
          ((((g⁻¹ : ↥Γ) : GL ι K)) : Matrix ι ι K)) *ᵥ v := by
        rw [hc, Matrix.mulVec_mulVec]
    _ = v := by
        rw [show ((g⁻¹ : ↥Γ) : GL ι K) = (g : GL ι K)⁻¹ by rfl]
        exact fs_mulVec_inv_mulVec (g : GL ι K) v

private lemma fs_eq_span_singleton_of_ne_zero_mem {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {F : Submodule K V} {x b : V} (hb : b ∈ F) (hb0 : b ≠ 0)
    (hle : F ≤ Submodule.span K {x}) : F = Submodule.span K {x} ∧ Nat.card ↥F = Nat.card K := by
  have hx : x ∈ F := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle hb)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hb0 hc.symm
    have hxb : x ∈ Submodule.span K ({b} : Set V) := by
      rw [Submodule.mem_span_singleton]
      exact ⟨c⁻¹, by rw [← hc, inv_smul_smul₀ hc0]⟩
    exact (Submodule.span_le.mpr (by simpa using hb)) hxb
  have hx0 : x ≠ 0 := by
    intro h0
    have : b ∈ Submodule.span K ({x} : Set V) := hle hb
    rw [h0] at this
    exact hb0 (by simpa using this)
  have hF : F = Submodule.span K {x} :=
    le_antisymm hle (Submodule.span_le.mpr (by simpa using hx))
  refine ⟨hF, ?_⟩
  rw [hF]
  haveI : Module.Finite K ↥(Submodule.span K {x}) := FiniteDimensional.span_singleton K x
  rw [Module.natCard_eq_pow_finrank (K := K), finrank_span_singleton hx0, pow_one]

private def fs_fixed {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (p : ℕ) {Γ : Subgroup (GL ι K)} (S : Sylow p ↥Γ) : Submodule K (ι → K) :=
  { carrier := {v | ∀ s ∈ (S : Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v}
    zero_mem' := by
      intro s _
      rw [Matrix.mulVec_zero]
    add_mem' := by
      intro x y hx hy s hs
      rw [Matrix.mulVec_add, hx s hs, hy s hs]
    smul_mem' := by
      intro c x hx s hs
      rw [Matrix.mulVec_smul, hx s hs] }

theorem exists_fixed_sylow_eq_span {ι K : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] {Γ : Subgroup (GL ι K)}
    (U : Subgroup ↥Γ) (hU : IsPGroup p ↥U) (e : ι → K)
    (hfix : ∀ v : ι → K,
      (∀ u ∈ U, ((u : GL ι K) : Matrix ι ι K) *ᵥ v = v) → v ∈ Submodule.span K {e})
    (S : Sylow p ↥Γ) :
    ∃ x : ↥Γ, ∀ v : ι → K,
      (∀ s ∈ (S : Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        v ∈ Submodule.span K {((x : GL ι K) : Matrix ι ι K) *ᵥ e} := by
  classical
  let F : Submodule K (ι → K) := fs_fixed p S
  have hcardF : Nat.card ↥F = Nat.card K := by
    change Nat.card
        {v : ι → K // ∀ s ∈ (S : Subgroup ↥Γ),
          ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v} = Nat.card K
    exact card_fixed_sylow_eq_card p U hU e hfix S
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Γ) P S
  have hgS : (S : Subgroup ↥Γ) = MulAut.conj g • (P : Subgroup ↥Γ) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hF_le : F ≤ Submodule.span K {(((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e} :=
    fun v hv => fs_mem_span_conj_of_fixed U P (S : Subgroup ↥Γ) hUP e hfix g hgS hv
  have hK2 : 1 < Nat.card K := Finite.one_lt_card
  have hF2 : 1 < Nat.card ↥F := hcardF.symm ▸ hK2
  have hnotsub : ¬ Subsingleton ↥F := by
    intro hsub
    have hle1 : Nat.card ↥F ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  haveI : Nontrivial ↥F := not_subsingleton_iff_nontrivial.mp hnotsub
  obtain ⟨a, b, hab⟩ := Nontrivial.exists_pair_ne (α := ↥F)
  have hb0 : ((a : ι → K) - (b : ι → K)) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hab (Subtype.ext h))
  have hbm : ((a : ι → K) - (b : ι → K)) ∈ F := F.sub_mem a.2 b.2
  have hF_eq : F = Submodule.span K {(((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e} :=
    (fs_eq_span_singleton_of_ne_zero_mem hbm hb0 hF_le).1
  refine ⟨g, fun v => ?_⟩
  rw [← hF_eq]
  exact Iff.rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

end
