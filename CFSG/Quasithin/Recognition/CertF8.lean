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

structure GF8 where
  val : Fin 8

instance : DecidableEq GF8 := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; simp_all)
  else isFalse (fun e => h (e ▸ rfl))

namespace GF8

@[expose] def ofNat' (n : ℕ) : GF8 := ⟨⟨n % 8, Nat.mod_lt n (by norm_num)⟩⟩

@[expose] def toNat (a : GF8) : ℕ := a.val.val

@[expose] def mulNat (a b : ℕ) : ℕ :=
  let r := (if b &&& 1 = 1 then a else 0) ^^^ (if b &&& 2 = 2 then a <<< 1 else 0) ^^^
    (if b &&& 4 = 4 then a <<< 2 else 0)
  let r := if r &&& 16 = 16 then r ^^^ 22 else r
  if r &&& 8 = 8 then r ^^^ 11 else r

instance : Zero GF8 := ⟨ofNat' 0⟩

instance : One GF8 := ⟨ofNat' 1⟩

instance : Add GF8 := ⟨fun a b => ofNat' (a.toNat ^^^ b.toNat)⟩

instance : Neg GF8 := ⟨fun a => a⟩

instance : Mul GF8 := ⟨fun a b => ofNat' (mulNat a.toNat b.toNat)⟩

instance : Inv GF8 :=
  ⟨fun a => ofNat' (mulNat (mulNat a.toNat a.toNat) (mulNat (mulNat a.toNat a.toNat)
    (mulNat a.toNat a.toNat)))⟩

instance : Fintype GF8 :=
  Fintype.ofEquiv (Fin 8) ⟨GF8.mk, GF8.val, fun _ => rfl, fun _ => rfl⟩

instance : Field GF8 :=
  Field.ofMinimalAxioms GF8 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end GF8

end CFSG.Quasithin
