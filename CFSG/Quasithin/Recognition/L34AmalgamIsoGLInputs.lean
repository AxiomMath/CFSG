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

namespace CFSG.Quasithin.L34Amalgam

@[expose] def bxor (x y : Fin 16) : Fin 16 := ⟨(x.val ^^^ y.val) % 16, Nat.mod_lt _ (by norm_num)⟩

@[expose] def bit (i : Fin 4) (x : Fin 16) : Bool := x.val / 2 ^ i.val % 2 == 1

@[expose] def sel (b : Bool) (m : Fin 16) : Fin 16 := if b then m else 0

@[expose] def lin (m : Fin 4 → Fin 16) (x : Fin 16) : Fin 16 :=
  bxor (bxor (sel (bit 0 x) (m 0)) (sel (bit 1 x) (m 1)))
    (bxor (sel (bit 2 x) (m 2)) (sel (bit 3 x) (m 3)))

@[expose] def refA : Fin 4 → Fin 16 := ![4, 8, 1, 2]

@[expose] def refB : Fin 4 → Fin 16 := ![2, 3, 14, 7]

@[expose] def conjMap (u v : Fin 4 → Fin 16) (w : Fin 16) : Fin 4 → Fin 16 :=
  ![w, lin v w, lin u w, lin u (lin v w)]

@[expose] def ofCode (k : ℕ) : Fin 4 → Fin 16 :=
  ![⟨k % 16, Nat.mod_lt _ (by norm_num)⟩, ⟨k / 16 % 16, Nat.mod_lt _ (by norm_num)⟩,
    ⟨k / 256 % 16, Nat.mod_lt _ (by norm_num)⟩, ⟨k / 4096 % 16, Nat.mod_lt _ (by norm_num)⟩]

@[expose] def basisVec : Fin 4 → Fin 16 := ![1, 2, 4, 8]

@[expose] def checkPair (u v : Fin 4 → Fin 16) : Bool :=
  if (List.finRange 4).all (fun i => (lin u ∘ lin v)^[5] (basisVec i) == basisVec i) then
    (List.finRange 16).any fun w =>
      let T := conjMap u v w
      (List.finRange 16).all (fun x => x == 0 || lin T x != 0) &&
        (List.finRange 4).all (fun i => lin T (refA i) == lin u (T i)) &&
        (List.finRange 4).all (fun i => lin T (refB i) == lin v (T i))
  else true

end CFSG.Quasithin.L34Amalgam
