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
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
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

namespace CFSG.RankThree.Native.ONTriple

open Equiv Equiv.Perm

@[expose] def sK1 : Perm (Fin 6) := c[0, 3, 1]

@[expose] def sK2 : Perm (Fin 6) := c[0, 5, 2] * c[1, 3, 4]

@[expose] def sY (j : ℕ) : Perm (Fin 6) := if j = 0 then c[0, 2, 1] else c[0, 2, 1] * c[3, 4, 5]

@[expose] def sV (j m i : ℕ) : Perm (Fin 6) :=
  ((([[[c[0, 1] * c[2, 4], c[0, 2] * c[1, 4], c[0, 4] * c[1, 2]],
      [c[0, 1] * c[2, 3], c[0, 2] * c[1, 3], c[0, 3] * c[1, 2]],
      [c[0, 1] * c[2, 5], c[0, 2] * c[1, 5], c[0, 5] * c[1, 2]]],
    [[c[1, 5] * c[2, 4], c[0, 3] * c[2, 4], c[0, 3] * c[1, 5]],
      [c[1, 3] * c[2, 5], c[0, 4] * c[2, 5], c[0, 4] * c[1, 3]],
      [c[1, 4] * c[2, 3], c[0, 5] * c[2, 3], c[0, 5] * c[1, 4]]]] :
    List (List (List (Perm (Fin 6))))).getD j []).getD m []).getD i 1

@[expose] def cj (κ t : Perm (Fin 6)) : Perm (Fin 6) := κ⁻¹ * t * κ

@[expose] def stepFin (gens : List (Perm (Fin 6))) (S : Finset (Perm (Fin 6))) :
    Finset (Perm (Fin 6)) :=
  S ∪ S.biUnion fun x => (gens.map (x * ·)).toFinset

@[expose] def closureFin (gens : List (Perm (Fin 6))) : ℕ → Finset (Perm (Fin 6))
  | 0 => {1}
  | n + 1 => stepFin gens (closureFin gens n)

@[expose, irreducible] def cl360 : Finset (Perm (Fin 6)) := closureFin [sK1, sK2] 16

@[expose] def cand1 (κ t : Perm (Fin 6)) : List (Perm (Fin 6)) :=
  [t * cj κ t, t * t * cj κ t, t * t * t * cj κ t]

@[expose] def cand2 (κ s : Perm (Fin 6)) (V : List (Perm (Fin 6))) : List (Perm (Fin 6)) :=
  (V.map (s * ·)) ++ (V.map fun v => cj κ s * (s * v)) ++
    [s * cj κ s, s * cj κ (cj κ s), s * cj κ s * cj κ (cj κ s)]

end CFSG.RankThree.Native.ONTriple
