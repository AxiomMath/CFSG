module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv

theorem normal_sym_six (N : Subgroup (Perm (Fin 6))) [N.Normal] :
    Nat.card N ≤ 2 ∨ 360 ∣ Nat.card N := by
  classical
  let A : Subgroup (Perm (Fin 6)) := alternatingGroup (Fin 6)
  have hsimple : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  have hnorm : (N.subgroupOf A).Normal := Subgroup.Normal.subgroupOf inferInstance A
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
  · left
    have hdis : Disjoint N A := Subgroup.subgroupOf_eq_bot.1 h
    have hinj : Function.Injective ((QuotientGroup.mk' A).comp N.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [eq_bot_iff]
      intro n hn
      have hnA : (n : Perm (Fin 6)) ∈ A := by
        have : (QuotientGroup.mk' A) (n : Perm (Fin 6)) = 1 := hn
        exact (QuotientGroup.eq_one_iff _).1 this
      have := hdis.le_bot ⟨n.2, hnA⟩
      rw [Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have h1 := Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card (Perm (Fin 6) ⧸ A) = 2 := by
      rw [← Subgroup.index]
      have := Subgroup.index_mul_card A
      have h3 : Nat.card ↥A = 360 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Fintype.card_fin, Nat.factorial]
      have h4 : Nat.card (Perm (Fin 6)) = 720 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm]
        simp [Nat.factorial]
      rw [h3, h4] at this
      omega
    rwa [h2] at h1
  · right
    have hle : A ≤ N := Subgroup.subgroupOf_eq_top.1 h
    have h3 : Nat.card ↥A = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Fintype.card_fin, Nat.factorial]
    rw [← h3]
    exact Subgroup.card_dvd_of_le hle

theorem sym_six_index_ne (H : Subgroup (Perm (Fin 6))) (h : H.index = 3 ∨ H.index = 5) :
    False := by
  classical
  have hfi : H.FiniteIndex := ⟨by omega⟩
  have hNn : H.normalCore.Normal := inferInstance
  have hd1 : H.normalCore.index ∣ Nat.factorial H.index :=
    H.index_normalCore_dvd_factorial_index
  have hd2 : H.index ∣ H.normalCore.index := Subgroup.index_dvd_of_le H.normalCore_le
  have h4 : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have hcard : H.normalCore.index * Nat.card H.normalCore = 720 := by
    rw [Subgroup.index_mul_card, h4]
  have hN := normal_sym_six H.normalCore
  generalize H.normalCore.index = i at hd1 hd2 hcard
  generalize Nat.card H.normalCore = n at hN hcard
  rcases h with h | h <;> rw [h] at hd1 hd2
  · have : i ≤ 6 := Nat.le_of_dvd (by norm_num [Nat.factorial]) hd1
    interval_cases i <;> omega
  · have : i ≤ 120 := Nat.le_of_dvd (by norm_num [Nat.factorial]) hd1
    interval_cases i <;> omega

theorem isCoatom_of_index_fifteen (K : Subgroup (Perm (Fin 6))) (hK : K.index = 15) :
    IsCoatom K := by
  refine ⟨fun h => ?_, fun H hKH => ?_⟩
  · rw [h, Subgroup.index_top] at hK
    omega
  · have hd : H.index ∣ K.index := Subgroup.index_dvd_of_le hKH.le
    rw [hK] at hd
    have hle : H.index ≤ 15 := Nat.le_of_dvd (by norm_num) hd
    have h1 := Subgroup.relIndex_mul_index hKH.le
    have hpos : 0 < H.index := Nat.pos_of_ne_zero (fun h0 => by
      rw [h0] at hd
      omega)
    interval_cases hi : H.index <;> first | omega | skip
    · exact Subgroup.index_eq_one.1 hi
    · exact (sym_six_index_ne H (Or.inl hi)).elim
    · exact (sym_six_index_ne H (Or.inr hi)).elim
    · exfalso
      rw [hK] at h1
      have h2 : K.relIndex H = 1 := by omega
      exact (ne_of_lt hKH) ((Subgroup.relIndex_eq_one.1 h2).antisymm hKH.le).symm

end CFSG.Quasithin.F6.GoldAmS
