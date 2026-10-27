module

public import TauCeti.GroupTheory.Perm.FinThree.Basic
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

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c11_big_modelb_map_subtype_normalizer {U : Type*} [Group U]
    (K : Subgroup U) (Y' : Subgroup ↥K) (hY' : Y'.Normal) :
    K ≤ Subgroup.normalizer (Y'.map K.subtype : Set U) := by
  rw [Subgroup.le_set_normalizer_iff]
  intro k hk y hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  exact Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * y' * ⟨k, hk⟩⁻¹, hY'.conj_mem y' hy' ⟨k, hk⟩,
    by simp [map_mul, map_inv]⟩

theorem s16c11_big_modelb_three_card {U : Type*} [Group U]
    {K : Subgroup U} (s : ↥K ≃* Equiv.Perm (Fin 3)) :
    Nat.card (((alternatingGroup (Fin 3)).comap s.toMonoidHom).map K.subtype) = 3 := by
  have h1 := Subgroup.card_map_of_injective (f := s.toMonoidHom) s.injective
    (K := (alternatingGroup (Fin 3)).comap s.toMonoidHom)
  rw [Subgroup.map_comap_eq_self_of_surjective s.surjective] at h1
  rw [Subgroup.card_map_of_injective (K := (alternatingGroup (Fin 3)).comap s.toMonoidHom)
    K.subtype_injective, ← h1, TauCeti.card_alternatingGroup_fin_three]

theorem s16c11_big_modelb_three_mem_of_centralizer {U : Type*} [Group U]
    {K : Subgroup U} (s : ↥K ≃* Equiv.Perm (Fin 3)) {κ : U} (hκ : κ ∈ K)
    (hc : κ ∈ Subgroup.centralizer
      (((alternatingGroup (Fin 3)).comap s.toMonoidHom).map K.subtype : Set U)) :
    κ ∈ ((alternatingGroup (Fin 3)).comap s.toMonoidHom).map K.subtype := by
  have hsκcent : s ⟨κ, hκ⟩ ∈ Subgroup.centralizer
      (alternatingGroup (Fin 3) : Set (Equiv.Perm (Fin 3))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro τ hτ
    let k' : ↥K := s.symm τ
    have hsk' : s k' = τ := s.apply_symm_apply τ
    have hk'Y' : k' ∈ (alternatingGroup (Fin 3)).comap s.toMonoidHom :=
      Subgroup.mem_comap.mpr (by simpa [hsk'] using hτ)
    have hy : K.subtype k' ∈ ((alternatingGroup (Fin 3)).comap s.toMonoidHom).map K.subtype :=
      Subgroup.mem_map.mpr ⟨k', hk'Y', rfl⟩
    have hcomm : K.subtype k' * κ = κ * K.subtype k' :=
      Subgroup.mem_centralizer_iff.mp hc (K.subtype k') hy
    have hkeq : k' * ⟨κ, hκ⟩ = ⟨κ, hκ⟩ * k' := by
      apply K.subtype_injective
      rw [map_mul, map_mul]
      simpa using hcomm
    calc τ * s ⟨κ, hκ⟩ = s k' * s ⟨κ, hκ⟩ := by rw [hsk']
      _ = s (k' * ⟨κ, hκ⟩) := by rw [map_mul]
      _ = s (⟨κ, hκ⟩ * k') := by rw [hkeq]
      _ = s ⟨κ, hκ⟩ * s k' := by rw [map_mul]
      _ = s ⟨κ, hκ⟩ * τ := by rw [hsk']
  have hsκA : s ⟨κ, hκ⟩ ∈ alternatingGroup (Fin 3) :=
    TauCeti.centralizer_alternatingGroup_fin_three_le hsκcent
  exact Subgroup.mem_map.mpr ⟨⟨κ, hκ⟩, Subgroup.mem_comap.mpr hsκA, rfl⟩

theorem s16c11_big_modelb_three_pow_three {U : Type*} [Group U]
    {K : Subgroup U} (s : ↥K ≃* Equiv.Perm (Fin 3)) {κ : U} (hκ : κ ∈ K)
    (hY : κ ∈ ((alternatingGroup (Fin 3)).comap s.toMonoidHom).map K.subtype) :
    κ ^ 3 = 1 := by
  obtain ⟨k', hk', hk'eq⟩ := Subgroup.mem_map.mp hY
  have hsκA : s k' ∈ alternatingGroup (Fin 3) := Subgroup.mem_comap.mp hk'
  have h3' : (⟨s k', hsκA⟩ : ↥(alternatingGroup (Fin 3))) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(alternatingGroup (Fin 3))) (x := ⟨s k', hsκA⟩)
    simpa only [TauCeti.card_alternatingGroup_fin_three] using h
  have h3 : (s k') ^ 3 = 1 := by
    have h := congrArg (fun z : ↥(alternatingGroup (Fin 3)) =>
      (z : Equiv.Perm (Fin 3))) h3'
    simpa using h
  have hk'3 : k' ^ 3 = 1 := by
    apply s.injective
    simpa [map_pow] using h3
  have hthis : ((K.subtype k') ^ 3 : U) = 1 := by
    have h := congrArg (fun z : ↥K => (z : U)) hk'3
    simpa [map_pow] using h
  rwa [hk'eq] at hthis

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
