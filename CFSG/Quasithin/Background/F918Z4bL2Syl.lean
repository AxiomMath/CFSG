module

import CFSG.Walter.Bender1970.S2.AutEven
import CFSG.Walter.PSL2Facts.Even
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
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

namespace CFSG.Quasithin

open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups Pointwise

theorem mulAut_eq_of_smul_sylow_eq {f : ℕ} (hf : f ≠ 0)
    {α β : MulAut PSL(2, GaloisField 2 f)}
    (h : ∀ Q : Sylow 2 PSL(2, GaloisField 2 f), α • Q = β • Q) : α = β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply psl2MulAutProjectiveLine_injective (GaloisField 2 f) (GaloisField.card 2 f hf)
  ext x
  rw [psl2MulAutProjectiveLine_apply, psl2MulAutProjectiveLine_apply, h]

theorem mulAut_eq_conj_of_fixes_sylow {f : ℕ} (hf : 2 ≤ f) (S : Sylow 2 PSL(2, GaloisField 2 f))
    (hS : ∀ a ∈ (S : Subgroup PSL(2, GaloisField 2 f)),
      ∀ b ∈ (S : Subgroup PSL(2, GaloisField 2 f)), a * b = b * a)
    (φ : MulAut PSL(2, GaloisField 2 f))
    (hφ : ∀ x ∈ (S : Subgroup PSL(2, GaloisField 2 f)), φ x = x) :
    ∃ s ∈ (S : Subgroup PSL(2, GaloisField 2 f)), φ = MulAut.conj s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := PSL(2, GaloisField 2 f) with hLdef
  have hf0 : f ≠ 0 := by omega
  have hcomm' : ∀ (g : L) (P : Sylow 2 L), φ • (g • P) = (φ g) • (φ • P) := by
    intro g P
    apply Sylow.ext
    ext x
    rw [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul,
      Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have key : (MulAut.conj g)⁻¹ • (φ⁻¹ • x) = φ⁻¹ • ((MulAut.conj (φ g))⁻¹ • x) := by
      simp only [MulAut.smul_def, MulAut.conj_inv_apply, map_mul, map_inv, MulAut.inv_apply_self]
    rw [key]
  have hcomm : ∀ s ∈ (S : Subgroup L), ∀ P : Sylow 2 L, φ • (s • P) = s • (φ • P) := by
    intro s hs P
    rw [hcomm', hφ s hs]
  have hφS' : φ • S = S := by
    apply Sylow.ext
    ext x
    rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
    constructor
    · intro hx
      have h1 := hφ _ hx
      rw [MulAut.apply_inv_self] at h1
      rw [h1]
      exact hx
    · intro hx
      have h1 := hφ _ hx
      have h2 : φ⁻¹ x = x := by
        conv_lhs => rw [← h1]
        exact MulAut.inv_apply_self _ φ x
      rw [h2]
      exact hx
  have hφS'' : φ⁻¹ • S = S := by
    conv_lhs => rw [← hφS']
    rw [inv_smul_smul]
  have horbit : ∀ P₀ : Sylow 2 L, P₀ ≠ S → ∀ P : Sylow 2 L, P ≠ S →
      ∃ s ∈ (S : Subgroup L), s • P₀ = P := by
    intro P₀ hP₀
    have hne : ∀ s ∈ (S : Subgroup L), s • P₀ ≠ S := by
      intro s hs h
      apply hP₀
      have h1 : s⁻¹ • S = S :=
        Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ((S : Subgroup L).inv_mem hs))
      calc P₀ = s⁻¹ • (s • P₀) := (inv_smul_smul s P₀).symm
        _ = s⁻¹ • S := by rw [h]
        _ = S := h1
    let g : ↥(S : Subgroup L) → {P : Sylow 2 L // P ≠ S} := fun s =>
      ⟨(s : L) • P₀, hne s s.2⟩
    have hg : Function.Injective g := by
      intro s s' hss'
      have h1 : (s : L) • P₀ = (s' : L) • P₀ := congrArg Subtype.val hss'
      have h2 : ((s' : L)⁻¹ * s) • P₀ = P₀ := by rw [mul_smul, h1, inv_smul_smul]
      rw [Sylow.smul_eq_iff_mem_normalizer] at h2
      have h3 : (s' : L)⁻¹ * s ∈ Subgroup.normalizer ((P₀ : Subgroup L) : Set L) ⊓ S :=
        ⟨h2, (S : Subgroup L).mul_mem ((S : Subgroup L).inv_mem s'.2) s.2⟩
      rw [psl2_even_normalizer_inf_eq_bot hf hP₀, Subgroup.mem_bot, inv_mul_eq_one] at h3
      exact Subtype.ext h3.symm
    have hcardS : Nat.card (S : Subgroup L) = 2 ^ f := (psl2_even_sylow_two hf S).2
    have hcardP : Nat.card {P : Sylow 2 L // P ≠ S} = 2 ^ f := by
      have h1 := psl2_even_card_sylow hf0
      have : Fintype (Sylow 2 L) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card] at h1 ⊢
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, h1]
      omega
    have hbij : Function.Bijective g :=
      hg.bijective_of_nat_card_le (by rw [hcardS, hcardP])
    intro P hP
    obtain ⟨s, hs⟩ := hbij.2 ⟨P, hP⟩
    exact ⟨s, s.2, congrArg Subtype.val hs⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : Sylow 2 L, P₁ ≠ S := by
    have h1 : 1 < Nat.card (Sylow 2 L) := by
      rw [psl2_even_card_sylow hf0]
      exact Nat.lt_add_of_pos_left (Nat.two_pow_pos f)
    have : Nontrivial (Sylow 2 L) := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne S
  have hφP₁ : φ • P₁ ≠ S := by
    intro h
    apply hP₁
    calc P₁ = φ⁻¹ • (φ • P₁) := (inv_smul_smul φ P₁).symm
      _ = φ⁻¹ • S := by rw [h]
      _ = S := hφS''
  obtain ⟨s₁, hs₁, hs₁eq⟩ := horbit P₁ hP₁ (φ • P₁) hφP₁
  have hall : ∀ P : Sylow 2 L, φ • P = s₁ • P := by
    intro P
    by_cases hP : P = S
    · rw [hP, hφS']
      exact (Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hs₁)).symm
    · obtain ⟨s, hs, rfl⟩ := horbit P₁ hP₁ P hP
      rw [hcomm s hs, ← hs₁eq, ← mul_smul, ← mul_smul, hS s hs s₁ hs₁]
  refine ⟨s₁, hs₁, mulAut_eq_of_smul_sylow_eq hf0 fun P => ?_⟩
  rw [hall P]
  exact Sylow.smul_def.symm

end CFSG.Quasithin
