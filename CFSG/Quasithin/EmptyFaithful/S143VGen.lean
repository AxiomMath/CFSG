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

namespace CFSG.Quasithin.S143V

theorem relIndex_sup_of_inf_eq_bot {R : Type*} [Group R] [Finite R] {N P : Subgroup R} [N.Normal]
    (hNP : N ⊓ P = ⊥) : P.relIndex (N ⊔ P) = Nat.card N := by
  have h1 : N.relIndex (N ⊔ P) = N.relIndex P := Subgroup.relIndex_sup_left (H := P) (K := N)
  have h2 : N.relIndex P = Nat.card P := by
    rw [← Subgroup.inf_relIndex_right N P, hNP, Subgroup.relIndex_bot_left]
  have h3 := Subgroup.relIndex_mul_card N (N ⊔ P)
  have h4 := Subgroup.relIndex_mul_card P (N ⊔ P)
  rw [inf_eq_left.mpr le_sup_left] at h3
  rw [inf_eq_left.mpr le_sup_right] at h4
  rw [h1, h2] at h3
  have hP : 0 < Nat.card P := Nat.card_pos
  have : P.relIndex (N ⊔ P) * Nat.card P = Nat.card N * Nat.card P := by
    rw [h4, ← h3, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hP this

theorem relIndex_comap_sup_map {H S : Type*} [Group H] [Group S] [Finite S] (ρ : H →* S)
    {T : Subgroup H} (hker : ρ.ker ≤ T) {N : Subgroup S} (hNr : N ≤ ρ.range)
    (hNn : ∀ s ∈ ρ.range, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hNT : ∀ x ∈ N, x ∈ T.map ρ → x = 1) :
    T.relIndex (Subgroup.comap ρ (N ⊔ T.map ρ)) = Nat.card N := by
  set P := T.map ρ with hP
  have hPr : P ≤ ρ.range := Subgroup.map_le_range ρ T
  have hTP : Subgroup.comap ρ P = T := by
    rw [hP, Subgroup.comap_map_eq, sup_eq_left.mpr hker]
  have hle : N ⊔ P ≤ ρ.range := sup_le hNr hPr
  have step1 : T.relIndex (Subgroup.comap ρ (N ⊔ P)) = P.relIndex (N ⊔ P) := by
    conv_lhs => rw [← hTP]
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  rw [step1]
  have : Finite ρ.range := inferInstance
  have hnorm : (N.subgroupOf ρ.range).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn⟩
  have hNP' : N.subgroupOf ρ.range ⊓ P.subgroupOf ρ.range = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hNT _ hx.1 hx.2)
  have h5 : P.relIndex (N ⊔ P) = (P.subgroupOf ρ.range).relIndex (N.subgroupOf ρ.range ⊔
      P.subgroupOf ρ.range) := by
    rw [← Subgroup.subgroupOf_sup hNr hPr]
    exact (Subgroup.relIndex_subgroupOf hle).symm
  rw [h5, relIndex_sup_of_inf_eq_bot hNP']
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNr).toEquiv

theorem exists_mem_comap_of_mem {H S : Type*} [Group H] [Group S] (ρ : H →* S)
    {J : Subgroup S} {n : S} (hn : n ∈ ρ.range) (hnJ : n ∈ J) :
    ∃ x : H, x ∈ Subgroup.comap ρ J ∧ ρ x = n := by
  obtain ⟨x, rfl⟩ := hn
  exact ⟨x, hnJ, rfl⟩

end CFSG.Quasithin.S143V
