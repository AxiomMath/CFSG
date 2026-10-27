module

public import CFSG.RankThree.PartOne.A6N.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.Batch14971

open CFSG.RankThree.PartOne.A6N Equiv

theorem centralizer_a₀ :
    ∀ x : Perm (Fin 6), x * a₀ = a₀ * x → ∃ i : Fin 5, x = a₀ ^ (i : ℕ) := by
  decide +kernel

theorem solutions : ∀ y : Perm (Fin 6), (y * a₀) ^ 3 = 1 → (y * a₀⁻¹) ^ 4 = 1 → (y * s₀) ^ 5 = 1 →
    (y * (a₀ * s₀)) ^ 2 = 1 → y = y₀ ∨ y = y₁ := by
  decide +kernel

def gen : Fin 3 → alternatingGroup (Fin 6) := ![a₀A, s₀A, y₀A]

def ev (w : List (Fin 3)) : alternatingGroup (Fin 6) := (w.map gen).prod

def table : List (List (Fin 3)) := [
  [], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 0], [1, 2], [2, 0], [2, 1], [2, 2], [0, 0, 0],
  [0, 0, 1], [0, 0, 2], [0, 1, 2], [0, 2, 0], [0, 2, 1], [0, 2, 2], [1, 0, 0], [1, 0, 1],
  [1, 0, 2], [1, 2, 0], [1, 2, 1], [1, 2, 2], [2, 0, 0], [2, 0, 1], [2, 0, 2], [2, 1, 0],
  [2, 1, 2], [2, 2, 0], [2, 2, 1], [0, 0, 0, 2], [0, 0, 1, 2], [0, 0, 2, 0], [0, 0, 2, 1],
  [0, 0, 2, 2], [0, 2, 0, 0], [0, 2, 0, 1], [0, 2, 0, 2], [0, 2, 1, 0], [0, 2, 1, 2],
  [0, 2, 2, 0], [0, 2, 2, 1], [1, 0, 0, 2], [1, 0, 1, 2], [1, 0, 2, 0], [1, 0, 2, 1],
  [1, 0, 2, 2], [1, 2, 0, 0], [1, 2, 0, 1], [1, 2, 0, 2], [1, 2, 1, 0], [1, 2, 1, 2],
  [1, 2, 2, 0], [1, 2, 2, 1], [2, 0, 0, 0], [2, 0, 0, 2], [2, 0, 2, 2], [2, 1, 0, 0],
  [2, 1, 0, 1], [2, 1, 0, 2], [2, 1, 2, 0], [2, 1, 2, 1], [2, 1, 2, 2], [2, 2, 0, 0],
  [2, 2, 0, 2], [2, 2, 1, 0], [2, 2, 1, 2], [0, 0, 0, 2, 0], [0, 0, 0, 2, 1], [0, 0, 0, 2, 2],
  [0, 0, 2, 0, 0], [0, 0, 2, 0, 1], [0, 0, 2, 0, 2], [0, 0, 2, 1, 0], [0, 0, 2, 1, 2],
  [0, 0, 2, 2, 0], [0, 0, 2, 2, 1], [0, 2, 0, 0, 0], [0, 2, 0, 0, 2], [0, 2, 0, 2, 2],
  [0, 2, 1, 0, 0], [0, 2, 1, 0, 1], [0, 2, 1, 0, 2], [0, 2, 1, 2, 0], [0, 2, 1, 2, 1],
  [0, 2, 1, 2, 2], [0, 2, 2, 0, 0], [0, 2, 2, 0, 2], [0, 2, 2, 1, 0], [0, 2, 2, 1, 2],
  [1, 0, 2, 0, 0], [1, 0, 2, 0, 2], [1, 0, 2, 1, 0], [1, 0, 2, 1, 2], [1, 2, 0, 0, 0],
  [1, 2, 0, 0, 2], [1, 2, 0, 2, 2], [1, 2, 1, 0, 0], [1, 2, 1, 0, 1], [1, 2, 1, 0, 2],
  [1, 2, 1, 2, 0], [1, 2, 1, 2, 1], [1, 2, 1, 2, 2], [1, 2, 2, 0, 0], [1, 2, 2, 0, 2],
  [1, 2, 2, 1, 0], [1, 2, 2, 1, 2], [2, 0, 0, 0, 2], [2, 0, 0, 2, 0], [2, 0, 0, 2, 1],
  [2, 0, 0, 2, 2], [2, 0, 2, 2, 0], [2, 0, 2, 2, 1], [2, 1, 0, 0, 2], [2, 1, 0, 1, 2],
  [2, 1, 0, 2, 0], [2, 1, 0, 2, 1], [2, 1, 0, 2, 2], [2, 1, 2, 0, 0], [2, 1, 2, 0, 1],
  [2, 1, 2, 0, 2], [2, 1, 2, 1, 0], [2, 1, 2, 1, 2], [2, 1, 2, 2, 0], [2, 1, 2, 2, 1],
  [2, 2, 0, 0, 0], [2, 2, 0, 0, 2], [2, 2, 0, 2, 2], [2, 2, 1, 0, 0], [2, 2, 1, 0, 2],
  [2, 2, 1, 2, 2], [0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 2], [0, 0, 0, 2, 1, 0],
  [0, 0, 0, 2, 1, 2], [0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 2], [0, 0, 2, 0, 2, 2],
  [0, 0, 2, 1, 0, 0], [0, 0, 2, 1, 0, 1], [0, 0, 2, 1, 0, 2], [0, 0, 2, 1, 2, 0],
  [0, 0, 2, 1, 2, 1], [0, 0, 2, 1, 2, 2], [0, 0, 2, 2, 0, 0], [0, 0, 2, 2, 0, 2],
  [0, 0, 2, 2, 1, 0], [0, 0, 2, 2, 1, 2], [0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0],
  [0, 2, 0, 0, 2, 1], [0, 2, 0, 0, 2, 2], [0, 2, 0, 2, 2, 0], [0, 2, 0, 2, 2, 1],
  [0, 2, 1, 0, 0, 2], [0, 2, 1, 0, 1, 2], [0, 2, 1, 0, 2, 0], [0, 2, 1, 0, 2, 2],
  [0, 2, 1, 2, 0, 0], [0, 2, 1, 2, 0, 1], [0, 2, 1, 2, 0, 2], [0, 2, 1, 2, 1, 0],
  [0, 2, 1, 2, 2, 0], [0, 2, 1, 2, 2, 1], [0, 2, 2, 0, 0, 0], [0, 2, 2, 0, 0, 2],
  [0, 2, 2, 0, 2, 2], [0, 2, 2, 1, 0, 0], [0, 2, 2, 1, 0, 2], [0, 2, 2, 1, 2, 2],
  [1, 0, 2, 0, 0, 0], [1, 0, 2, 0, 0, 2], [1, 0, 2, 1, 0, 0], [1, 0, 2, 1, 0, 1],
  [1, 0, 2, 1, 0, 2], [1, 0, 2, 1, 2, 0], [1, 0, 2, 1, 2, 1], [1, 0, 2, 1, 2, 2],
  [1, 2, 0, 0, 0, 2], [1, 2, 0, 0, 2, 0], [1, 2, 0, 0, 2, 1], [1, 2, 0, 0, 2, 2],
  [1, 2, 1, 0, 0, 2], [1, 2, 1, 0, 1, 2], [1, 2, 1, 0, 2, 0], [1, 2, 1, 0, 2, 1],
  [1, 2, 1, 0, 2, 2], [1, 2, 1, 2, 0, 0], [1, 2, 1, 2, 0, 1], [1, 2, 1, 2, 0, 2],
  [1, 2, 1, 2, 2, 0], [1, 2, 1, 2, 2, 1], [1, 2, 2, 0, 0, 0], [1, 2, 2, 0, 0, 2],
  [1, 2, 2, 0, 2, 2], [1, 2, 2, 1, 0, 0], [1, 2, 2, 1, 0, 2], [1, 2, 2, 1, 2, 2],
  [2, 0, 0, 0, 2, 1], [2, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 1],
  [2, 0, 0, 2, 0, 2], [2, 0, 0, 2, 1, 0], [2, 0, 0, 2, 1, 2], [2, 0, 0, 2, 2, 0],
  [2, 0, 2, 2, 1, 2], [2, 1, 0, 2, 0, 0], [2, 1, 0, 2, 0, 2], [2, 1, 0, 2, 1, 0],
  [2, 1, 2, 0, 0, 0], [2, 1, 2, 0, 0, 2], [2, 1, 2, 0, 2, 2], [2, 1, 2, 1, 0, 0],
  [2, 1, 2, 1, 0, 1], [2, 1, 2, 1, 2, 2], [2, 1, 2, 2, 0, 0], [2, 1, 2, 2, 1, 0],
  [2, 1, 2, 2, 1, 2], [2, 2, 0, 0, 0, 2], [2, 2, 0, 0, 2, 0], [2, 2, 0, 0, 2, 1],
  [2, 2, 0, 2, 2, 0], [2, 2, 0, 2, 2, 1], [2, 2, 1, 0, 0, 2], [2, 2, 1, 0, 2, 0],
  [2, 2, 1, 0, 2, 1], [2, 2, 1, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2],
  [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 2, 1, 0, 1], [0, 0, 0, 2, 1, 0, 2], [0, 0, 0, 2, 1, 2, 0],
  [0, 0, 0, 2, 1, 2, 1], [0, 0, 0, 2, 1, 2, 2], [0, 0, 2, 0, 0, 0, 2], [0, 0, 2, 0, 0, 2, 0],
  [0, 0, 2, 0, 0, 2, 1], [0, 0, 2, 0, 0, 2, 2], [0, 0, 2, 0, 2, 2, 1], [0, 0, 2, 1, 0, 0, 2],
  [0, 0, 2, 1, 0, 1, 2], [0, 0, 2, 1, 0, 2, 0], [0, 0, 2, 1, 0, 2, 2], [0, 0, 2, 1, 2, 0, 1],
  [0, 0, 2, 1, 2, 0, 2], [0, 0, 2, 1, 2, 2, 0], [0, 0, 2, 1, 2, 2, 1], [0, 0, 2, 2, 0, 0, 0],
  [0, 0, 2, 2, 0, 0, 2], [0, 0, 2, 2, 0, 2, 2], [0, 0, 2, 2, 1, 0, 0], [0, 0, 2, 2, 1, 0, 2],
  [0, 2, 0, 0, 0, 2, 2], [0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 2, 0, 1], [0, 2, 0, 0, 2, 1, 0],
  [0, 2, 0, 0, 2, 2, 0], [0, 2, 1, 0, 2, 0, 0], [0, 2, 1, 0, 2, 0, 2], [0, 2, 1, 2, 1, 0, 1],
  [0, 2, 1, 2, 2, 0, 0], [0, 2, 1, 2, 2, 1, 0], [0, 2, 1, 2, 2, 1, 2], [0, 2, 2, 0, 0, 0, 2],
  [0, 2, 2, 0, 0, 2, 0], [0, 2, 2, 0, 0, 2, 1], [0, 2, 2, 1, 0, 0, 2], [0, 2, 2, 1, 0, 2, 0],
  [0, 2, 2, 1, 0, 2, 1], [0, 2, 2, 1, 0, 2, 2], [1, 0, 2, 0, 0, 0, 2], [1, 0, 2, 0, 0, 2, 1],
  [1, 0, 2, 0, 0, 2, 2], [1, 0, 2, 1, 0, 0, 2], [1, 0, 2, 1, 0, 2, 0], [1, 0, 2, 1, 0, 2, 2],
  [1, 0, 2, 1, 2, 2, 1], [1, 2, 0, 0, 0, 2, 2], [1, 2, 0, 0, 2, 1, 0], [1, 2, 0, 0, 2, 2, 0],
  [1, 2, 1, 0, 2, 0, 0], [1, 2, 1, 0, 2, 0, 2], [1, 2, 1, 2, 2, 0, 0], [1, 2, 1, 2, 2, 1, 0],
  [1, 2, 1, 2, 2, 1, 2], [1, 2, 2, 0, 0, 0, 2], [1, 2, 2, 0, 0, 2, 0], [1, 2, 2, 0, 0, 2, 1],
  [1, 2, 2, 1, 0, 0, 2], [1, 2, 2, 1, 0, 2, 0], [1, 2, 2, 1, 0, 2, 1], [2, 0, 0, 0, 2, 1, 0],
  [2, 0, 0, 2, 1, 0, 1], [2, 0, 0, 2, 1, 2, 0], [2, 0, 0, 2, 1, 2, 2], [2, 0, 0, 2, 2, 0, 0],
  [2, 0, 0, 2, 2, 0, 2], [2, 1, 0, 2, 0, 0, 0], [2, 1, 0, 2, 0, 0, 2], [2, 1, 0, 2, 1, 0, 0],
  [2, 1, 2, 0, 0, 2, 2], [2, 1, 2, 1, 2, 2, 0], [2, 1, 2, 1, 2, 2, 1], [2, 1, 2, 2, 0, 0, 0],
  [2, 1, 2, 2, 0, 0, 2], [2, 1, 2, 2, 1, 0, 0], [2, 1, 2, 2, 1, 0, 2], [2, 2, 0, 0, 0, 2, 1],
  [2, 2, 0, 0, 0, 2, 2], [2, 2, 0, 0, 2, 0, 0], [2, 2, 0, 0, 2, 0, 1], [2, 2, 0, 0, 2, 0, 2],
  [2, 2, 0, 0, 2, 1, 0], [2, 2, 0, 2, 2, 1, 2], [2, 2, 1, 0, 2, 0, 0], [2, 2, 1, 0, 2, 1, 0],
  [0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 2, 0, 0, 2, 1], [0, 0, 0, 2, 1, 0, 2, 0],
  [0, 0, 2, 0, 0, 0, 2, 2], [0, 0, 2, 0, 0, 2, 1, 0], [0, 0, 2, 0, 0, 2, 2, 0],
  [0, 0, 2, 1, 0, 2, 0, 0], [0, 0, 2, 1, 0, 2, 0, 2], [0, 0, 2, 1, 2, 2, 1, 0],
  [0, 0, 2, 2, 0, 0, 0, 2], [0, 0, 2, 2, 0, 0, 2, 0], [0, 0, 2, 2, 1, 0, 0, 2],
  [0, 0, 2, 2, 1, 0, 2, 1], [0, 2, 0, 0, 2, 2, 0, 0], [0, 2, 1, 0, 2, 0, 0, 2],
  [0, 2, 1, 2, 2, 0, 0, 0], [0, 2, 1, 2, 2, 0, 0, 2], [0, 2, 1, 2, 2, 1, 0, 0],
  [0, 2, 1, 2, 2, 1, 0, 2], [0, 2, 2, 0, 0, 0, 2, 1], [0, 2, 2, 0, 0, 0, 2, 2],
  [0, 2, 2, 0, 0, 2, 0, 0], [0, 2, 2, 0, 0, 2, 0, 1], [0, 2, 2, 1, 0, 2, 0, 0],
  [0, 2, 2, 1, 0, 2, 1, 0], [1, 0, 2, 0, 0, 0, 2, 2], [1, 0, 2, 1, 0, 2, 0, 0],
  [1, 0, 2, 1, 0, 2, 0, 2], [1, 0, 2, 1, 2, 2, 1, 0], [1, 0, 2, 1, 2, 2, 1, 2],
  [1, 2, 1, 2, 2, 0, 0, 0], [1, 2, 1, 2, 2, 1, 0, 0], [1, 2, 2, 0, 0, 2, 0, 1],
  [1, 2, 2, 0, 0, 2, 0, 2], [1, 2, 2, 1, 0, 2, 1, 0], [2, 0, 0, 2, 2, 0, 2, 2],
  [0, 0, 0, 2, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 2, 1, 0], [0, 0, 2, 2, 0, 0, 2, 0, 1],
  [0, 0, 2, 2, 1, 0, 2, 1, 0]
  ]

theorem table_length : table.length = 360 := by decide +kernel

theorem table_nodup : (table.map ev).Nodup := by decide +kernel

theorem gen_mem (i : Fin 3) :
    gen i ∈ Subgroup.closure ({a₀A, s₀A, y₀A} : Set (alternatingGroup (Fin 6))) := by
  fin_cases i
  · exact Subgroup.subset_closure (by simp [gen])
  · exact Subgroup.subset_closure (by simp [gen])
  · exact Subgroup.subset_closure (by simp [gen])

theorem ev_mem (w : List (Fin 3)) :
    ev w ∈ Subgroup.closure ({a₀A, s₀A, y₀A} : Set (alternatingGroup (Fin 6))) := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact gen_mem i

theorem closure_eq_top :
    Subgroup.closure ({a₀A, s₀A, y₀A} : Set (alternatingGroup (Fin 6))) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hcard : (table.map ev).toFinset.card = Fintype.card (alternatingGroup (Fin 6)) := by
    rw [List.toFinset_card_of_nodup table_nodup, List.length_map, table_length,
      card_alternatingGroup, Fintype.card_fin]
    decide +kernel
  have huniv : (table.map ev).toFinset = Finset.univ := Finset.eq_univ_of_card _ hcard
  have hg : g ∈ (table.map ev).toFinset := by rw [huniv]; exact Finset.mem_univ g
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hg)
  exact ev_mem w

end CertificateChecks.Batch14971

namespace Certificates

open CFSG.RankThree.PartOne.A6N Equiv

open CFSG.RankThree.PartOne.A6N Equiv in
theorem certificate14971 : (∀ x : Perm (Fin 6), x * a₀ = a₀ * x → ∃ i : Fin 5, x = a₀ ^ (i : ℕ)) ∧
    (∀ y : Perm (Fin 6), (y * a₀) ^ 3 = 1 → (y * a₀⁻¹) ^ 4 = 1 → (y * s₀) ^ 5 = 1 →
      (y * (a₀ * s₀)) ^ 2 = 1 → y = y₀ ∨ y = y₁) ∧
    Subgroup.closure ({a₀A, s₀A, y₀A} : Set (alternatingGroup (Fin 6))) = ⊤ :=
  ⟨CertificateChecks.Batch14971.centralizer_a₀, CertificateChecks.Batch14971.solutions, CertificateChecks.Batch14971.closure_eq_top⟩

end Certificates
