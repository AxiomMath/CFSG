module

public import Mathlib.Algebra.Field.MinimalAxioms
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

namespace CFSG.Quasithin

structure GF9 where
  val : Fin 9

instance : DecidableEq GF9 := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; simp_all)
  else isFalse (fun e => h (e ▸ rfl))

namespace GF9

@[expose] def ofNat' (n : ℕ) : GF9 := ⟨⟨n % 9, Nat.mod_lt n (by norm_num)⟩⟩

@[expose] def toNat (a : GF9) : ℕ := a.val.val

@[expose] def mulNat (x y : ℕ) : ℕ :=
  (x % 3 * (y % 3) + 2 * (x / 3 % 3) * (y / 3 % 3)) % 3 +
    3 * ((x % 3 * (y / 3 % 3) + x / 3 % 3 * (y % 3)) % 3)

@[expose] def addNat (x y : ℕ) : ℕ := (x % 3 + y % 3) % 3 + 3 * ((x / 3 % 3 + y / 3 % 3) % 3)

@[expose] def negNat (x : ℕ) : ℕ := (3 - x % 3) % 3 + 3 * ((3 - x / 3 % 3) % 3)

instance : Zero GF9 := ⟨ofNat' 0⟩

instance : One GF9 := ⟨ofNat' 1⟩

instance : Add GF9 := ⟨fun a b => ofNat' (addNat a.toNat b.toNat)⟩

instance : Neg GF9 := ⟨fun a => ofNat' (negNat a.toNat)⟩

instance : Mul GF9 := ⟨fun a b => ofNat' (mulNat a.toNat b.toNat)⟩

instance : Inv GF9 :=
  ⟨fun a => ofNat' (mulNat (mulNat (mulNat a.toNat a.toNat) (mulNat a.toNat a.toNat))
    (mulNat (mulNat a.toNat a.toNat) a.toNat))⟩

instance : Fintype GF9 :=
  Fintype.ofEquiv (Fin 9) ⟨GF9.mk, GF9.val, fun _ => rfl, fun _ => rfl⟩

instance : Field GF9 :=
  Field.ofMinimalAxioms GF9 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end GF9

end CFSG.Quasithin
