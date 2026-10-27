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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.Quasithin.RuType

structure F4 where
  code : Fin 4

namespace F4

instance : DecidableEq F4 := fun x y =>
  decidable_of_iff (x.code = y.code) (by cases x; cases y; simp)

@[expose] def equivFin : F4 ≃ Fin 4 where
  toFun := code
  invFun := mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance : Fintype F4 := Fintype.ofEquiv (Fin 4) equivFin.symm

@[expose] def add (x y : F4) : F4 := ⟨x.code ^^^ y.code⟩

@[expose] def mulCode (x y : Fin 4) : Fin 4 :=
  let a0 := x.val % 2
  let a1 := x.val / 2
  let b0 := y.val % 2
  let b1 := y.val / 2
  ⟨(a0 * b0 + a1 * b1) % 2 + 2 * ((a0 * b1 + a1 * b0 + a1 * b1) % 2), by omega⟩

@[expose] def mul (x y : F4) : F4 := ⟨mulCode x.code y.code⟩

instance : Zero F4 := ⟨⟨0⟩⟩
instance : One F4 := ⟨⟨1⟩⟩
instance : Add F4 := ⟨add⟩
instance : Mul F4 := ⟨mul⟩
instance : Neg F4 := ⟨id⟩
instance : Sub F4 := ⟨add⟩
instance : Inv F4 := ⟨fun x => mul x x⟩
instance : Div F4 := ⟨fun x y => mul x (mul y y)⟩

@[expose] def ω : F4 := ⟨2⟩

instance instCommRing : CommRing F4 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  neg_add_cancel := by decide
  mul_comm := by decide
  sub_eq_add_neg := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

instance instField : Field F4 where
  mul_inv_cancel := by decide
  inv_zero := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  div_eq_mul_inv := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

theorem card : Fintype.card F4 = 4 := by decide

theorem two_eq_zero : (2 : F4) = 0 := by decide

instance : CharP F4 2 := by
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
  exact two_eq_zero

theorem sq_sq : ∀ x : F4, (x ^ 2) ^ 2 = x := by decide

end F4

end CFSG.Quasithin.RuType
