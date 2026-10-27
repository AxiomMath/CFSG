module

import CFSG.Quasithin.AppendixH.H9.H93.S8Part1.OddInvolutions
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
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv

private def gs03Alt8RefTwo : Perm (Fin 8) := swap 0 1

private def gs03Alt8RefThree : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5

private def gs03Alt8WitTwoPerm (i : Fin 7) : Perm (Fin 8) :=
  if i = 0 then 1 else if i = 1 then swap 0 1 * swap 0 2 else swap 0 i.castSucc * swap 1 i.succ

private lemma gs03Alt8WitTwoPerm_mem (i : Fin 7) :
    gs03Alt8WitTwoPerm i ∈ alternatingGroup (Fin 8) := by
  fin_cases i <;> rw [Equiv.Perm.mem_alternatingGroup] <;> decide

private def gs03Alt8WitTwo (i : Fin 7) : alternatingGroup (Fin 8) :=
  ⟨gs03Alt8WitTwoPerm i, gs03Alt8WitTwoPerm_mem i⟩

private lemma gs03Alt8WitTwo_conj (i : Fin 7) :
    ((gs03Alt8WitTwo i : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ * gs03Alt8RefTwo *
      ((gs03Alt8WitTwo i : alternatingGroup (Fin 8)) : Perm (Fin 8)) = swap i.castSucc i.succ := by
  fin_cases i <;> decide

private lemma gs03Alt8WitTwo_le :
    alternatingGroup (Fin 8) ≤ Subgroup.closure (Set.range fun i : Fin 7 =>
      ((gs03Alt8WitTwo i : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ * gs03Alt8RefTwo *
        ((gs03Alt8WitTwo i : alternatingGroup (Fin 8)) : Perm (Fin 8))) := by
  have hf : (fun i : Fin 7 => ((gs03Alt8WitTwo i : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ *
      gs03Alt8RefTwo * ((gs03Alt8WitTwo i : alternatingGroup (Fin 8)) : Perm (Fin 8))) =
      (fun i : Fin 7 => swap i.castSucc i.succ) := by
    funext i
    exact gs03Alt8WitTwo_conj i
  rw [hf]
  rw [Subgroup.closure_eq_top_of_mclosure_eq_top (Perm.mclosure_swap_castSucc_succ 7)]
  exact le_top

private def gs03Alt8TThreeList : List (Perm (Fin 8)) :=
  [List.formPerm [1, 2, 3, 6, 7],
   List.formPerm [3, 4, 6, 5, 7],
   List.formPerm [1, 6] * List.formPerm [2, 7, 5, 3],
   List.formPerm [0, 7, 1] * List.formPerm [2, 6, 3],
   List.formPerm [0, 7, 3, 1] * List.formPerm [5, 6],
   List.formPerm [1, 7, 5, 3, 2],
   List.formPerm [3, 7, 6, 5, 4]]

private def gs03Alt8TThree (i : Fin 7) : Perm (Fin 8) := gs03Alt8TThreeList[i]

private lemma gs03Alt8TThree_mem (i : Fin 7) : gs03Alt8TThree i ∈ alternatingGroup (Fin 8) := by
  fin_cases i <;> rw [Equiv.Perm.mem_alternatingGroup] <;> decide

private def gs03Alt8WitThree (i : Fin 7) : alternatingGroup (Fin 8) :=
  ⟨gs03Alt8TThree i, gs03Alt8TThree_mem i⟩

private def gs03Alt8AThree (i : Fin 7) : Perm (Fin 8) :=
  ((gs03Alt8WitThree i : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ * gs03Alt8RefThree *
    ((gs03Alt8WitThree i : alternatingGroup (Fin 8)) : Perm (Fin 8))

private def gs03Alt8Hthree : Subgroup (Perm (Fin 8)) := Subgroup.closure (Set.range gs03Alt8AThree)

private lemma gs03Alt8AThree_mem (i : Fin 7) : gs03Alt8AThree i ∈ gs03Alt8Hthree :=
  Subgroup.subset_closure ⟨i, rfl⟩

private lemma gs03Alt8Sigma_eq : gs03Alt8AThree 0 * gs03Alt8AThree 1 * gs03Alt8AThree 2 =
    (List.formPerm [0, 3, 4, 1, 7, 5, 6, 2] : Perm (Fin 8)) := by
  have h0 : gs03Alt8AThree 0 = (List.formPerm [0, 7] * List.formPerm [1, 2] *
      List.formPerm [4, 5] : Perm (Fin 8)) := by decide
  have h1 : gs03Alt8AThree 1 = (List.formPerm [0, 1] * List.formPerm [2, 7] *
      List.formPerm [3, 6] : Perm (Fin 8)) := by decide
  have h2 : gs03Alt8AThree 2 = (List.formPerm [0, 6] * List.formPerm [3, 5] *
      List.formPerm [4, 7] : Perm (Fin 8)) := by decide
  have h01 : (List.formPerm [0, 7] * List.formPerm [1, 2] *
        List.formPerm [4, 5] : Perm (Fin 8)) *
      (List.formPerm [0, 1] * List.formPerm [2, 7] *
        List.formPerm [3, 6] : Perm (Fin 8)) =
      (List.formPerm [0, 2] * List.formPerm [1, 7] * List.formPerm [3, 6] *
        List.formPerm [4, 5] : Perm (Fin 8)) := by decide
  have h012 : (List.formPerm [0, 2] * List.formPerm [1, 7] * List.formPerm [3, 6] *
        List.formPerm [4, 5] : Perm (Fin 8)) *
      (List.formPerm [0, 6] * List.formPerm [3, 5] *
        List.formPerm [4, 7] : Perm (Fin 8)) =
      (List.formPerm [0, 3, 4, 1, 7, 5, 6, 2] : Perm (Fin 8)) := by decide
  rw [h0, h1, h2, h01, h012]

private lemma gs03Alt8Tau_eq : gs03Alt8AThree 0 * gs03Alt8AThree 3 * gs03Alt8AThree 1 =
    (swap 1 7 : Perm (Fin 8)) := by
  have h0 : gs03Alt8AThree 0 = (List.formPerm [0, 7] * List.formPerm [1, 2] *
      List.formPerm [4, 5] : Perm (Fin 8)) := by decide
  have h3 : gs03Alt8AThree 3 = (List.formPerm [1, 7] * List.formPerm [3, 6] *
      List.formPerm [4, 5] : Perm (Fin 8)) := by decide
  have h1 : gs03Alt8AThree 1 = (List.formPerm [0, 1] * List.formPerm [2, 7] *
      List.formPerm [3, 6] : Perm (Fin 8)) := by decide
  have h03 : (List.formPerm [0, 7] * List.formPerm [1, 2] *
        List.formPerm [4, 5] : Perm (Fin 8)) *
      (List.formPerm [1, 7] * List.formPerm [3, 6] *
        List.formPerm [4, 5] : Perm (Fin 8)) =
      (List.formPerm [0, 7, 2, 1] * List.formPerm [3, 6] : Perm (Fin 8)) := by decide
  have h031 : (List.formPerm [0, 7, 2, 1] * List.formPerm [3, 6] : Perm (Fin 8)) *
      (List.formPerm [0, 1] * List.formPerm [2, 7] *
        List.formPerm [3, 6] : Perm (Fin 8)) =
      (swap 1 7 : Perm (Fin 8)) := by decide
  rw [h0, h3, h1, h03, h031]

private lemma gs03Alt8WitThree_le :
    alternatingGroup (Fin 8) ≤ Subgroup.closure (Set.range fun i : Fin 7 =>
      ((gs03Alt8WitThree i : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ * gs03Alt8RefThree *
        ((gs03Alt8WitThree i : alternatingGroup (Fin 8)) : Perm (Fin 8))) := by
  have hsig_mem : gs03Alt8AThree 0 * gs03Alt8AThree 1 * gs03Alt8AThree 2 ∈ gs03Alt8Hthree :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (gs03Alt8AThree_mem 0) (gs03Alt8AThree_mem 1))
      (gs03Alt8AThree_mem 2)
  have htau_mem : gs03Alt8AThree 0 * gs03Alt8AThree 3 * gs03Alt8AThree 1 ∈ gs03Alt8Hthree :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (gs03Alt8AThree_mem 0) (gs03Alt8AThree_mem 3))
      (gs03Alt8AThree_mem 1)
  have hcycle : (gs03Alt8AThree 0 * gs03Alt8AThree 1 * gs03Alt8AThree 2).IsCycle := by
    rw [gs03Alt8Sigma_eq]
    exact List.isCycle_formPerm (by decide) (by decide)
  have hsupp : (gs03Alt8AThree 0 * gs03Alt8AThree 1 * gs03Alt8AThree 2).support = Finset.univ := by
    rw [gs03Alt8Sigma_eq]
    decide
  have htop : Subgroup.closure ({gs03Alt8AThree 0 * gs03Alt8AThree 1 * gs03Alt8AThree 2,
      swap 1 ((gs03Alt8AThree 0 * gs03Alt8AThree 1 * gs03Alt8AThree 2) 1)} :
      Set (Perm (Fin 8))) = ⊤ :=
    Equiv.Perm.closure_cycle_adjacent_swap hcycle hsupp 1
  have hsubset : ({gs03Alt8AThree 0 * gs03Alt8AThree 1 * gs03Alt8AThree 2,
      swap 1 ((gs03Alt8AThree 0 * gs03Alt8AThree 1 * gs03Alt8AThree 2) 1)} : Set (Perm (Fin 8))) ⊆
      gs03Alt8Hthree := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hsig_mem
    · have h1 : (gs03Alt8AThree 0 * gs03Alt8AThree 1 * gs03Alt8AThree 2) 1 = 7 := by
        rw [gs03Alt8Sigma_eq]
        decide
      rw [h1, ← gs03Alt8Tau_eq]
      exact htau_mem
  have : (⊤ : Subgroup (Perm (Fin 8))) ≤ gs03Alt8Hthree := by
    rw [← htop]
    exact (Subgroup.closure_le _).mpr hsubset
  exact le_trans le_top this

private lemma gs03Alt8ExistsWitnessOfConj {g r : Perm (Fin 8)} (hgsign : Perm.sign g = -1)
    {wit : Fin 7 → alternatingGroup (Fin 8)}
    (hwit : alternatingGroup (Fin 8) ≤ Subgroup.closure (Set.range fun i =>
      ((wit i : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ * r *
        ((wit i : alternatingGroup (Fin 8)) : Perm (Fin 8))))
    (hconj : IsConj g r) :
    ∃ s : Fin 7 → alternatingGroup (Fin 8),
      alternatingGroup (Fin 8) ≤ Subgroup.closure (Set.range fun i =>
        (((s i : alternatingGroup (Fin 8)) : Perm (Fin 8)))⁻¹ * g *
          ((s i : alternatingGroup (Fin 8)) : Perm (Fin 8))) := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  set d : Perm (Fin 8) := if c ∈ alternatingGroup (Fin 8) then c else c * g with hd
  have hd_mem : d ∈ alternatingGroup (Fin 8) := by
    rw [hd]
    by_cases hcA : c ∈ alternatingGroup (Fin 8)
    · rw [if_pos hcA]
      exact hcA
    · rw [if_neg hcA]
      rw [Equiv.Perm.mem_alternatingGroup] at hcA ⊢
      rw [map_mul, hgsign]
      rcases Int.units_eq_one_or (Perm.sign c) with h | h
      · exact absurd h hcA
      · rw [h]
        decide
  have hd_conj : g = d⁻¹ * r * d := by
    have hg_eq : g = c⁻¹ * r * c := by
      calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
        _ = c⁻¹ * r * c := by rw [hc]
    rw [hd]
    by_cases hcA : c ∈ alternatingGroup (Fin 8)
    · rw [if_pos hcA]
      exact hg_eq
    · rw [if_neg hcA]
      have h : (c * g)⁻¹ * r * (c * g) = g := by
        calc (c * g)⁻¹ * r * (c * g) = g⁻¹ * (c⁻¹ * r * c) * g := by group
          _ = g⁻¹ * g * g := by rw [hg_eq]
          _ = g := by group
      exact h.symm
  let s : Fin 7 → alternatingGroup (Fin 8) := fun i =>
    ⟨d⁻¹ * ((wit i : alternatingGroup (Fin 8)) : Perm (Fin 8)),
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hd_mem) (wit i).2⟩
  refine ⟨s, ?_⟩
  have hfun : (fun i => ((s i : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ * g *
      ((s i : alternatingGroup (Fin 8)) : Perm (Fin 8))) =
      (fun i => ((wit i : alternatingGroup (Fin 8)) : Perm (Fin 8))⁻¹ * r *
        ((wit i : alternatingGroup (Fin 8)) : Perm (Fin 8))) := by
    funext i
    have hs : ((s i : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
        d⁻¹ * ((wit i : alternatingGroup (Fin 8)) : Perm (Fin 8)) := rfl
    rw [hs, hd_conj]
    group
  rw [hfun]
  exact hwit

theorem gs03_alt8_odd_involution_gen (g : Perm (Fin 8)) (hg2 : g * g = 1)
    (hg : g ∉ alternatingGroup (Fin 8)) :
    ∃ s : Fin 7 → alternatingGroup (Fin 8),
      (alternatingGroup (Fin 8)) ≤ Subgroup.closure (Set.range fun i =>
        (((s i : alternatingGroup (Fin 8)) : Perm (Fin 8)))⁻¹ * g *
          ((s i : alternatingGroup (Fin 8)) : Perm (Fin 8))) := by
  have hg2' : g ^ 2 = 1 := by rw [pow_two]; exact hg2
  have hsign_ne : Perm.sign g ≠ 1 := fun h =>
    hg (Equiv.Perm.mem_alternatingGroup.mpr h)
  have hsign : Perm.sign g = -1 := by
    rcases Int.units_eq_one_or (Perm.sign g) with h | h
    · exact absurd h hsign_ne
    · exact h
  rcases CFSG.ASVolI.ChH.cycleType_eq_two_or_two_two_two hg2' hsign with hct | hct
  · have hconj : IsConj g (swap 0 1) := by
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hct,
        CFSG.ASVolI.ChH.cycleType_swap_zero_one]
    exact gs03Alt8ExistsWitnessOfConj hsign gs03Alt8WitTwo_le hconj
  · have hconj : IsConj g (swap 0 1 * swap 2 3 * swap 4 5) := by
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hct,
        CFSG.ASVolI.ChH.cycleType_swap_triple]
    exact gs03Alt8ExistsWitnessOfConj hsign gs03Alt8WitThree_le hconj

end CFSG.LocalAnalysis.WeakClosure81
