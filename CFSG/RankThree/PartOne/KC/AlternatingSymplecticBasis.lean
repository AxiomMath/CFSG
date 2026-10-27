module

import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
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
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.RankThree.PartOne

namespace KCAlternating

open Module Submodule
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def IsSymplecticBasis {n : ℕ} (B : BilinForm K V) (b : Basis (Fin n ⊕ Fin n) K V) :
    Prop :=
  (∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
    (∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
    ∀ i j, B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0

section Gram

variable {n : ℕ} {B : BilinForm K V} {b : Basis (Fin n ⊕ Fin n) K V}

theorem IsSymplecticBasis.apply_inr_inl (hB : B.IsAlt) (hb : IsSymplecticBasis B b) (i j : Fin n) :
    B (b (Sum.inr i)) (b (Sum.inl j)) = if i = j then -1 else 0 := by
  rw [← hB.neg_eq, hb.2.2 j i]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem IsSymplecticBasis.toMatrix_eq (hB : B.IsAlt) (hb : IsSymplecticBasis B b) :
    BilinForm.toMatrix b B = Matrix.fromBlocks 0 1 (-1) 0 := by
  ext x y
  rw [BilinForm.toMatrix_apply]
  rcases x with i | i <;> rcases y with j | j
  · simp [hb.1 i j]
  · simp [hb.2.2 i j, Matrix.one_apply]
  · rw [hb.apply_inr_inl hB]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  · simp [hb.2.1 i j]

theorem isSymplecticBasis_iff_toMatrix_eq (hB : B.IsAlt) :
    IsSymplecticBasis B b ↔ BilinForm.toMatrix b B = Matrix.fromBlocks 0 1 (-1) 0 := by
  refine ⟨fun hb => hb.toMatrix_eq hB, fun h => ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩⟩
  · have := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
    simpa [BilinForm.toMatrix_apply] using this
  · have := congrFun (congrFun h (Sum.inr i)) (Sum.inr j)
    simpa [BilinForm.toMatrix_apply] using this
  · have := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
    simpa [BilinForm.toMatrix_apply, Matrix.one_apply] using this

theorem IsSymplecticBasis.apply_eq (hB : B.IsAlt) (hb : IsSymplecticBasis B b) (x y : V) :
    B x y = ⇑(b.repr x) ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0).mulVec ⇑(b.repr y) := by
  rw [BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B, hb.toMatrix_eq hB]

end Gram

section Existence

theorem isSymplecticBasis_reindex_sumComm {n : ℕ} {B : BilinForm K V}
    {c : Basis (Fin n ⊕ Fin n) K V} (hc : ∀ x y, B (c x) (c y) = Matrix.J (Fin n) K x y) :
    IsSymplecticBasis B (c.reindex (Equiv.sumComm (Fin n) (Fin n))) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · simp [Basis.reindex_apply, hc, Matrix.J]
  · simp [Basis.reindex_apply, hc, Matrix.J]
  · simp [Basis.reindex_apply, hc, Matrix.J, Matrix.one_apply]

variable [FiniteDimensional K V] {B : BilinForm K V}

theorem exists_isSymplecticBasis (hB : B.IsAlt) (hBn : B.Nondegenerate) :
    ∃ (n : ℕ) (b : Basis (Fin n ⊕ Fin n) K V), finrank K V = 2 * n ∧ IsSymplecticBasis B b := by
  obtain ⟨m, c, hc⟩ := hB.exists_basis_toMatrix_eq_J hBn
  have hc' : ∀ x y, B (c x) (c y) = Matrix.J (Fin m) K x y := fun x y => by
    rw [← hc, BilinForm.toMatrix_apply]
  refine ⟨m, c.reindex (Equiv.sumComm (Fin m) (Fin m)), ?_, isSymplecticBasis_reindex_sumComm hc'⟩
  rw [finrank_eq_card_basis c]
  simp [two_mul]

theorem exists_isSymplecticBasis_of_apply_eq_one (hB : B.IsAlt) (hBn : B.Nondegenerate) {a b : V}
    (hab : B a b = 1) :
    ∃ (n : ℕ) (c : Basis (Fin (n + 1) ⊕ Fin (n + 1)) K V), finrank K V = 2 * (n + 1) ∧
      IsSymplecticBasis B c ∧ c (Sum.inl 0) = a ∧ c (Sum.inr 0) = b := by
  have hZ : (B.restrict (B.orthogonal (span K {b, a}))).IsAlt := fun z => hB.self_eq_zero z
  obtain ⟨m, c, hc⟩ := hZ.exists_basis_toMatrix_eq_J
    (hB.restrict_nondegenerate_orthogonal_span_pair (e := b) (f := a) hab hBn)
  have hc' : ∀ x y, B (c x) (c y) = Matrix.J (Fin m) K x y := fun x y => by
    rw [← hc, BilinForm.toMatrix_apply, BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  obtain ⟨d, hd, hdd⟩ := hB.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hBn
    (e := b) (f := a) hab c hc'
  refine ⟨m, d.reindex (Equiv.sumComm (Fin (m + 1)) (Fin (m + 1))), ?_,
    isSymplecticBasis_reindex_sumComm hd, ?_, ?_⟩
  · rw [finrank_eq_card_basis d]
    simp [two_mul]
  · simp [Basis.reindex_apply, hdd]
  · simp [Basis.reindex_apply, hdd]

end Existence

theorem exists_isometry_of_finrank_eq {V' : Type*} [AddCommGroup V'] [Module K V']
    [FiniteDimensional K V] [FiniteDimensional K V'] {B : BilinForm K V} {B' : BilinForm K V'}
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (hB' : B'.IsAlt) (hBn' : B'.Nondegenerate)
    (h : finrank K V = finrank K V') : ∃ φ : V ≃ₗ[K] V', ∀ x y, B' (φ x) (φ y) = B x y := by
  obtain ⟨n, b, hn, hb⟩ := exists_isSymplecticBasis hB hBn
  obtain ⟨n', b', hn', hb'⟩ := exists_isSymplecticBasis hB' hBn'
  obtain rfl : n = n' := by omega
  have hext : B'.compl₁₂ (b.equiv b' (Equiv.refl _) : V →ₗ[K] V')
      (b.equiv b' (Equiv.refl _) : V →ₗ[K] V') = B := by
    refine BilinForm.ext_basis b fun i j => ?_
    have h1 := congrFun (congrFun (hb.toMatrix_eq hB) i) j
    have h2 := congrFun (congrFun (hb'.toMatrix_eq hB') i) j
    rw [BilinForm.toMatrix_apply] at h1 h2
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply,
      h1, h2]
  exact ⟨b.equiv b' (Equiv.refl _), fun x y => by
    simpa using LinearMap.congr_fun₂ hext x y⟩

end KCAlternating

open Module KCAlternating

theorem alternating_symplectic_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hBn : B.Nondegenerate) :
    (∃ (n : ℕ) (b : Basis (Fin n ⊕ Fin n) K V), finrank K V = 2 * n ∧
        (∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
        (∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
        ∀ i j, B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) ∧
    (∀ (W : Type*) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
        (B' : LinearMap.BilinForm K W), B'.IsAlt → B'.Nondegenerate →
        finrank K W = finrank K V → ∃ φ : V ≃ₗ[K] W, ∀ x y, B' (φ x) (φ y) = B x y) ∧
    (∀ a b : V, B a b = 1 → ∃ (n : ℕ) (c : Basis (Fin (n + 1) ⊕ Fin (n + 1)) K V),
        finrank K V = 2 * (n + 1) ∧
        (∀ i j, B (c (Sum.inl i)) (c (Sum.inl j)) = 0) ∧
        (∀ i j, B (c (Sum.inr i)) (c (Sum.inr j)) = 0) ∧
        (∀ i j, B (c (Sum.inl i)) (c (Sum.inr j)) = if i = j then 1 else 0) ∧
        c (Sum.inl 0) = a ∧ c (Sum.inr 0) = b) :=
  ⟨exists_isSymplecticBasis hB hBn,
    fun _ _ _ _ _ hB' hBn' h => exists_isometry_of_finrank_eq hB hBn hB' hBn' h.symm,
    fun _ _ hab => by
      obtain ⟨n, c, hn, ⟨h1, h2, h3⟩, hc1, hc2⟩ :=
        exists_isSymplecticBasis_of_apply_eq_one hB hBn hab
      exact ⟨n, c, hn, h1, h2, h3, hc1, hc2⟩⟩

end CFSG.RankThree.PartOne
