module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import CFSG.Quasithin.Recognition.J2RecCzModel
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open Matrix MatrixGroups

@[ext] structure SL7 where
  a : ZMod 7
  b : ZMod 7
  c : ZMod 7
  d : ZMod 7
  det : a * d - b * c = 1

namespace SL7

instance : One SL7 := ⟨⟨1, 0, 0, 1, by simp⟩⟩

instance : Mul SL7 :=
  ⟨fun p q => ⟨p.a * q.a + p.b * q.c, p.a * q.b + p.b * q.d, p.c * q.a + p.d * q.c,
    p.c * q.b + p.d * q.d, by linear_combination (q.a * q.d - q.b * q.c) * p.det + q.det⟩⟩

instance : Inv SL7 := ⟨fun p => ⟨p.d, -p.b, -p.c, p.a, by linear_combination p.det⟩⟩

instance : Div SL7 := ⟨fun p q => p * q⁻¹⟩

instance : Pow SL7 ℕ := ⟨fun x n => npowRec n x⟩

instance : Pow SL7 ℤ := ⟨fun x n => zpowRec npowRec n x⟩

instance : DecidableEq SL7 := fun p q =>
  decidable_of_iff (p.a = q.a ∧ p.b = q.b ∧ p.c = q.c ∧ p.d = q.d)
    ⟨fun ⟨h1, h2, h3, h4⟩ => by ext <;> assumption, fun h => by simp [h]⟩

@[simp] theorem one_a : (1 : SL7).a = 1 := rfl
@[simp] theorem one_b : (1 : SL7).b = 0 := rfl
@[simp] theorem one_c : (1 : SL7).c = 0 := rfl
@[simp] theorem one_d : (1 : SL7).d = 1 := rfl
@[simp] theorem mul_a (p q : SL7) : (p * q).a = p.a * q.a + p.b * q.c := rfl
@[simp] theorem mul_b (p q : SL7) : (p * q).b = p.a * q.b + p.b * q.d := rfl
@[simp] theorem mul_c (p q : SL7) : (p * q).c = p.c * q.a + p.d * q.c := rfl
@[simp] theorem mul_d (p q : SL7) : (p * q).d = p.c * q.b + p.d * q.d := rfl
@[simp] theorem inv_a (p : SL7) : p⁻¹.a = p.d := rfl
@[simp] theorem inv_b (p : SL7) : p⁻¹.b = -p.b := rfl
@[simp] theorem inv_c (p : SL7) : p⁻¹.c = -p.c := rfl
@[simp] theorem inv_d (p : SL7) : p⁻¹.d = p.a := rfl

instance : Fintype SL7 :=
  Fintype.ofEquiv {q : ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 // q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1}
    { toFun := fun q => ⟨q.1.1, q.1.2.1, q.1.2.2.1, q.1.2.2.2, q.2⟩
      invFun := fun p => ⟨(p.a, p.b, p.c, p.d), p.det⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def toSL (q : SL7) : SL(2, ZMod 7) :=
  ⟨!![q.a, q.b; q.c, q.d], by simpa [Matrix.det_fin_two] using q.det⟩

theorem toSL_injective : Function.Injective toSL := by
  intro p q h
  have h1 := congrArg (fun A : SL(2, ZMod 7) => (A : Matrix (Fin 2) (Fin 2) (ZMod 7)) 0 0) h
  have h2 := congrArg (fun A : SL(2, ZMod 7) => (A : Matrix (Fin 2) (Fin 2) (ZMod 7)) 0 1) h
  have h3 := congrArg (fun A : SL(2, ZMod 7) => (A : Matrix (Fin 2) (Fin 2) (ZMod 7)) 1 0) h
  have h4 := congrArg (fun A : SL(2, ZMod 7) => (A : Matrix (Fin 2) (Fin 2) (ZMod 7)) 1 1) h
  simp [toSL] at h1 h2 h3 h4
  ext <;> assumption

theorem toSL_mul (p q : SL7) : toSL (p * q) = toSL p * toSL q := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem toSL_one : toSL 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toSL]

theorem toSL_inv (p : SL7) : toSL p⁻¹ = (toSL p)⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toSL, Matrix.adjugate_fin_two]

theorem toSL_div (p q : SL7) : toSL (p / q) = toSL p / toSL q := by
  show toSL (p * q⁻¹) = _
  rw [toSL_mul, toSL_inv, div_eq_mul_inv]

theorem toSL_npow (p : SL7) (n : ℕ) : toSL (p ^ n) = toSL p ^ n := by
  induction n with
  | zero => exact toSL_one
  | succ n ih =>
    show toSL (npowRec (n + 1) p) = _
    rw [npowRec, toSL_mul]
    have : toSL (npowRec n p) = toSL p ^ n := ih
    rw [this, pow_succ]

theorem toSL_zpow (p : SL7) (n : ℤ) : toSL (p ^ n) = toSL p ^ n := by
  cases n with
  | ofNat n =>
    show toSL (zpowRec npowRec (Int.ofNat n) p) = _
    rw [zpowRec, Int.ofNat_eq_natCast, zpow_natCast]
    exact toSL_npow p n
  | negSucc n =>
    show toSL (zpowRec npowRec (Int.negSucc n) p) = _
    rw [zpowRec, zpow_negSucc]
    rw [toSL_inv]
    congr 1
    exact toSL_npow p (n + 1)

instance : Group SL7 :=
  Function.Injective.group toSL toSL_injective toSL_one toSL_mul toSL_inv toSL_div toSL_npow
    toSL_zpow

theorem toSL_surjective : Function.Surjective toSL := by
  intro A
  refine ⟨⟨A 0 0, A 0 1, A 1 0, A 1 1, ?_⟩, ?_⟩
  · have := A.2
    rw [Matrix.det_fin_two] at this
    exact this
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toSL]

noncomputable def mulEquiv : SL7 ≃* SL(2, ZMod 7) :=
  MulEquiv.ofBijective (MonoidHom.mk' toSL toSL_mul) ⟨toSL_injective, toSL_surjective⟩

def negOne : SL7 := ⟨-1, 0, 0, -1, by simp⟩

theorem mulEquiv_negOne : mulEquiv negOne = -1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mulEquiv, MonoidHom.mk', toSL, negOne]

theorem mem_center_sl2_seven (A : SL(2, ZMod 7)) :
    A ∈ Subgroup.center SL(2, ZMod 7) ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro h
    revert A
    decide +kernel
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [Subgroup.mem_center_iff]
      intro g
      ext i j
      simp

theorem negOne_mul_negOne : negOne * negOne = 1 := by
  ext <;> simp [negOne]

theorem negOne_inv : negOne⁻¹ = negOne := by
  ext <;> simp [negOne]

def Z7 : Subgroup SL7 where
  carrier := {x | x = 1 ∨ x = negOne}
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · simp
    · simp
    · simp
    · exact Or.inl negOne_mul_negOne
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl)
    · left; simp
    · right; exact negOne_inv

theorem mem_Z7 (x : SL7) : x ∈ Z7 ↔ x = 1 ∨ x = negOne := Iff.rfl

theorem mem_Z7_iff_center (x : SL7) : x ∈ Z7 ↔ mulEquiv x ∈ Subgroup.center SL(2, ZMod 7) := by
  rw [mem_center_sl2_seven, mem_Z7]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (by rw [h, mulEquiv_negOne])
  · rintro (h | h)
    · exact Or.inl (mulEquiv.injective (by rw [h, map_one]))
    · exact Or.inr (mulEquiv.injective (by rw [h, mulEquiv_negOne]))

theorem map_Z7 : Z7.map mulEquiv.toMonoidHom = Subgroup.center SL(2, ZMod 7) := by
  ext A
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_Z7_iff_center x).mp hx
  · intro hA
    obtain ⟨x, rfl⟩ := mulEquiv.surjective A
    exact ⟨x, (mem_Z7_iff_center x).mpr hA, rfl⟩

instance : Z7.Normal where
  conj_mem n hn g := by
    rw [mem_Z7_iff_center] at hn ⊢
    have h := Subgroup.mem_center_iff.mp hn (mulEquiv g)
    rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
    exact hn

instance : DecidablePred (· ∈ Z7) := fun x => decidable_of_iff _ (mem_Z7 x).symm

end SL7

abbrev PSL7 : Type := SL7 ⧸ SL7.Z7

noncomputable def PSL7.mulEquiv : PSL7 ≃* PSL(2, ZMod 7) :=
  QuotientGroup.congr SL7.Z7 (Subgroup.center SL(2, ZMod 7)) SL7.mulEquiv SL7.map_Z7

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
