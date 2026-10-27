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

namespace CFSG.Sporadic.HN.Local

open Equiv Finset

@[expose] def IsCanon (S : Finset (Fin 12)) : Prop := S.card = 6 ∧ (0 : Fin 12) ∈ S

instance (S : Finset (Fin 12)) : Decidable (IsCanon S) := by unfold IsCanon; infer_instance

abbrev Part : Type := {S : Finset (Fin 12) // IsCanon S}

@[expose] def canon (U : Finset (Fin 12)) : Finset (Fin 12) := if (0 : Fin 12) ∈ U then U else Uᶜ

theorem canon_isCanon {U : Finset (Fin 12)} (hU : U.card = 6) : IsCanon (canon U) := by
  unfold canon
  split_ifs with h
  · exact ⟨hU, h⟩
  · refine ⟨?_, by simpa using h⟩
    rw [Finset.card_compl, hU, Fintype.card_fin]

theorem canon_compl (U : Finset (Fin 12)) : canon Uᶜ = canon U := by
  unfold canon
  by_cases h : (0 : Fin 12) ∈ U
  · have : (0 : Fin 12) ∉ Uᶜ := by simpa using h
    rw [ite_eq_right this, ite_eq_left h, compl_compl]
  · have : (0 : Fin 12) ∈ Uᶜ := by simpa using h
    rw [ite_eq_left this, ite_eq_right h]

theorem canon_eq_self {U : Finset (Fin 12)} (h : (0 : Fin 12) ∈ U) : canon U = U := by
  unfold canon; rw [ite_eq_left h]

theorem map_compl_perm (σ : Perm (Fin 12)) (U : Finset (Fin 12)) :
    (Uᶜ).map σ.toEmbedding = (U.map σ.toEmbedding)ᶜ := by
  ext x
  simp only [Finset.mem_map, Finset.mem_compl, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    exact ha (σ.injective hba ▸ hb)
  · intro hx
    refine ⟨σ.symm x, fun h => hx ⟨σ.symm x, h, by simp⟩, by simp⟩

theorem canon_map_canon (σ : Perm (Fin 12)) (U : Finset (Fin 12)) :
    canon ((canon U).map σ.toEmbedding) = canon (U.map σ.toEmbedding) := by
  unfold canon
  by_cases h : (0 : Fin 12) ∈ U
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, map_compl_perm]
    exact canon_compl _

@[expose] def partMap (σ : Perm (Fin 12)) (S : Part) : Part :=
  ⟨canon (S.1.map σ.toEmbedding), canon_isCanon (by rw [Finset.card_map]; exact S.2.1)⟩

theorem partMap_one (S : Part) : partMap 1 S = S := by
  apply Subtype.ext
  simp only [partMap]
  rw [show (1 : Perm (Fin 12)).toEmbedding = Function.Embedding.refl _ from rfl, Finset.map_refl]
  exact canon_eq_self S.2.2

theorem partMap_mul (σ τ : Perm (Fin 12)) (S : Part) :
    partMap (σ * τ) S = partMap σ (partMap τ S) := by
  apply Subtype.ext
  simp only [partMap]
  rw [canon_map_canon, Finset.map_map]
  rfl

instance : MulAction (Perm (Fin 12)) Part where
  smul := partMap
  one_smul := partMap_one
  mul_smul := partMap_mul

theorem smul_part_val (σ : Perm (Fin 12)) (S : Part) :
    (σ • S).1 = canon (S.1.map σ.toEmbedding) := rfl

end CFSG.Sporadic.HN.Local
