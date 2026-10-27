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

namespace CFSG.RankThree.PartOne.S11d

open scoped commutatorElement

class CentralCommutators (Q : Type*) [Group Q] : Prop where
  central : ∀ x y z : Q, ⁅x, y⁆ * z = z * ⁅x, y⁆

class ClassTwoExp (p : ℕ) (Q : Type*) [Group Q] : Prop extends CentralCommutators Q where
  prime : p.Prime
  ne_two : p ≠ 2
  pow_eq_one : ∀ x : Q, x ^ p = 1

section Basic

variable {Q : Type*} [Group Q] [CentralCommutators Q]

theorem CentralCommutators.commute (x y z : Q) : Commute ⁅x, y⁆ z :=
  CentralCommutators.central x y z

theorem CentralCommutators.commute_commutator (x y u v : Q) : Commute ⁅x, y⁆ ⁅u, v⁆ :=
  CentralCommutators.commute x y _

theorem CentralCommutators.comm_mul_left (x y z : Q) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have h : ⁅y, z⁆ * x = x * ⁅y, z⁆ := CentralCommutators.central y z x
  calc ⁅x * y, z⁆ = x * ⁅y, z⁆ * z * x⁻¹ * z⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅y, z⁆ * x * z * x⁻¹ * z⁻¹ := by rw [← h]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅x, z⁆ * ⁅y, z⁆ := (CentralCommutators.commute_commutator y z x z).eq

theorem CentralCommutators.comm_mul_right (x y z : Q) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h := CentralCommutators.comm_mul_left y z x
  have h2 : ⁅x, y * z⁆ = (⁅y * z, x⁆)⁻¹ := (commutatorElement_inv _ _).symm
  rw [h2, h, mul_inv_rev, commutatorElement_inv, commutatorElement_inv]
  exact (CentralCommutators.commute_commutator x z x y).eq

theorem CentralCommutators.comm_commutator_pow (x u v : Q) (n : ℕ) : ⁅x, ⁅u, v⁆ ^ n⁆ = 1 := by
  rw [commutatorElement_def]
  have h : ⁅u, v⁆ ^ n * x = x * ⁅u, v⁆ ^ n :=
    ((CentralCommutators.commute u v x).pow_left n).eq
  calc x * ⁅u, v⁆ ^ n * x⁻¹ * (⁅u, v⁆ ^ n)⁻¹ = ⁅u, v⁆ ^ n * x * x⁻¹ * (⁅u, v⁆ ^ n)⁻¹ := by
        rw [← h]
    _ = 1 := by group

theorem CentralCommutators.commute_comm_pow (x y z : Q) (k : ℕ) : Commute (⁅x, y⁆ ^ k) z :=
  (CentralCommutators.commute x y z).pow_left k

end Basic

theorem two_mul_half_aux {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 2 * ((p + 1) / 2) = p + 1 := by
  have h1 := hp.eq_two_or_odd
  omega

theorem baer_rearrange {M : Type*} [Monoid M] (A B C : M) (hca : C * A = A * C)
    (hcb : C * B = B * C) : A * (B * C) = C * (A * B) := by
  calc A * (B * C) = A * (C * B) := by rw [hcb]
    _ = (A * C) * B := (mul_assoc _ _ _).symm
    _ = (C * A) * B := by rw [hca]
    _ = C * (A * B) := mul_assoc _ _ _

section Assoc

variable {Q : Type*} [Group Q] [CentralCommutators Q]

theorem baer_assoc_aux (x y z : Q) (k : ℕ) :
    x * y * ⁅y, x⁆ ^ k * z * ⁅z, x * y * ⁅y, x⁆ ^ k⁆ ^ k =
      x * (y * z * ⁅z, y⁆ ^ k) * ⁅y * z * ⁅z, y⁆ ^ k, x⁆ ^ k := by
  have e1 : ⁅z, x * y * ⁅y, x⁆ ^ k⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
    rw [CentralCommutators.comm_mul_right, CentralCommutators.comm_mul_right,
      CentralCommutators.comm_commutator_pow, mul_one]
  have e0 : ⁅⁅z, y⁆ ^ k, x⁆ = 1 := by
    rw [← commutatorElement_inv, CentralCommutators.comm_commutator_pow, inv_one]
  have e2 : ⁅y * z * ⁅z, y⁆ ^ k, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
    rw [CentralCommutators.comm_mul_left, CentralCommutators.comm_mul_left, e0, mul_one]
  rw [e1, e2]
  have hz1 : ⁅y, x⁆ ^ k * z = z * ⁅y, x⁆ ^ k := (CentralCommutators.commute_comm_pow y x z k).eq
  have hbc : (⁅z, x⁆ * ⁅z, y⁆) ^ k = ⁅z, x⁆ ^ k * ⁅z, y⁆ ^ k :=
    (CentralCommutators.commute_commutator z x z y).mul_pow k
  have hab : (⁅y, x⁆ * ⁅z, x⁆) ^ k = ⁅y, x⁆ ^ k * ⁅z, x⁆ ^ k :=
    (CentralCommutators.commute_commutator y x z x).mul_pow k
  have hca : ⁅z, y⁆ ^ k * ⁅y, x⁆ ^ k = ⁅y, x⁆ ^ k * ⁅z, y⁆ ^ k :=
    ((CentralCommutators.commute_commutator z y y x).pow_pow k k).eq
  have hcb : ⁅z, y⁆ ^ k * ⁅z, x⁆ ^ k = ⁅z, x⁆ ^ k * ⁅z, y⁆ ^ k :=
    ((CentralCommutators.commute_commutator z y z x).pow_pow k k).eq
  calc x * y * ⁅y, x⁆ ^ k * z * (⁅z, x⁆ * ⁅z, y⁆) ^ k
      = x * y * (⁅y, x⁆ ^ k * z) * (⁅z, x⁆ ^ k * ⁅z, y⁆ ^ k) := by rw [hbc]; simp only [mul_assoc]
    _ = x * y * z * (⁅y, x⁆ ^ k * (⁅z, x⁆ ^ k * ⁅z, y⁆ ^ k)) := by rw [hz1]; simp only [mul_assoc]
    _ = x * y * z * (⁅z, y⁆ ^ k * (⁅y, x⁆ ^ k * ⁅z, x⁆ ^ k)) := by
        rw [baer_rearrange _ _ _ hca hcb]
    _ = x * (y * z * ⁅z, y⁆ ^ k) * (⁅y, x⁆ * ⁅z, x⁆) ^ k := by rw [hab]; simp only [mul_assoc]

end Assoc

section Baer

@[expose] def Baer (p : ℕ) (Q : Type*) [Group Q] [ClassTwoExp p Q] : Type _ := Q

namespace Baer

variable {p : ℕ} {Q : Type*} [Group Q] [ClassTwoExp p Q]

@[expose] def mk (x : Q) : Baer p Q := x

@[expose] def val (x : Baer p Q) : Q := x

@[simp] theorem val_mk (x : Q) : val (mk (p := p) x) = x := rfl

@[simp] theorem mk_val (x : Baer p Q) : mk (val x) = x := rfl

theorem ext {x y : Baer p Q} (h : val x = val y) : x = y := h

instance : Add (Baer p Q) := ⟨fun x y => mk (val x * val y * ⁅val y, val x⁆ ^ ((p + 1) / 2))⟩

instance : Zero (Baer p Q) := ⟨mk 1⟩

instance : Neg (Baer p Q) := ⟨fun x => mk (val x)⁻¹⟩

theorem val_add (x y : Baer p Q) :
    val (x + y) = val x * val y * ⁅val y, val x⁆ ^ ((p + 1) / 2) := rfl

theorem val_zero : val (0 : Baer p Q) = 1 := rfl

theorem comm_pow_half_sq (x y : Q) :
    ⁅x, y⁆ ^ ((p + 1) / 2) * ⁅x, y⁆ ^ ((p + 1) / 2) = ⁅x, y⁆ := by
  rw [← pow_add, ← two_mul, two_mul_half_aux (ClassTwoExp.prime (p := p) (Q := Q))
    (ClassTwoExp.ne_two (p := p) (Q := Q)), pow_succ,
    ClassTwoExp.pow_eq_one (p := p) ⁅x, y⁆, one_mul]

instance : AddCommGroup (Baer p Q) where
  add_assoc x y z := ext (baer_assoc_aux (val x) (val y) (val z) ((p + 1) / 2))
  zero_add x := ext (by
    show 1 * val x * ⁅val x, 1⁆ ^ ((p + 1) / 2) = val x
    simp)
  add_zero x := ext (by
    show val x * 1 * ⁅1, val x⁆ ^ ((p + 1) / 2) = val x
    simp)
  add_comm x y := ext (by
    show val x * val y * ⁅val y, val x⁆ ^ ((p + 1) / 2) =
      val y * val x * ⁅val x, val y⁆ ^ ((p + 1) / 2)
    have hxy : val x * val y = ⁅val x, val y⁆ * (val y * val x) := by
      simp only [commutatorElement_def]; group
    have hc : ⁅val y, val x⁆ = ⁅val x, val y⁆⁻¹ := (commutatorElement_inv _ _).symm
    have hcen : ⁅val x, val y⁆ * (val y * val x) = (val y * val x) * ⁅val x, val y⁆ :=
      CentralCommutators.central _ _ _
    have hsq := comm_pow_half_sq (p := p) (val x) (val y)
    rw [hxy, hcen, mul_assoc, hc, inv_pow]
    congr 1
    calc ⁅val x, val y⁆ * (⁅val x, val y⁆ ^ ((p + 1) / 2))⁻¹
        = (⁅val x, val y⁆ ^ ((p + 1) / 2) * ⁅val x, val y⁆ ^ ((p + 1) / 2)) *
            (⁅val x, val y⁆ ^ ((p + 1) / 2))⁻¹ := by rw [hsq]
      _ = ⁅val x, val y⁆ ^ ((p + 1) / 2) := mul_inv_cancel_right _ _)
  neg_add_cancel x := ext (by
    show (val x)⁻¹ * val x * ⁅val x, (val x)⁻¹⁆ ^ ((p + 1) / 2) = 1
    simp [commutatorElement_def])
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem val_nsmul (n : ℕ) (x : Baer p Q) : val (n • x) = val x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, val_zero, pow_zero]
  | succ n ih =>
    rw [succ_nsmul, val_add, ih]
    have : ⁅val x, val x ^ n⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((Commute.refl (val x)).pow_right n).eq
    rw [this, one_pow, mul_one, pow_succ]

theorem nsmul_prime_eq_zero (x : Baer p Q) : p • x = 0 :=
  ext (by rw [val_nsmul]; exact ClassTwoExp.pow_eq_one (p := p) (val x))

@[expose] def addMap (f : Q →* Q) : Baer p Q →+ Baer p Q where
  toFun x := mk (f (val x))
  map_zero' := ext (by show f 1 = 1; exact f.map_one)
  map_add' x y := ext (by
    show f (val x * val y * ⁅val y, val x⁆ ^ ((p + 1) / 2)) =
      f (val x) * f (val y) * ⁅f (val y), f (val x)⁆ ^ ((p + 1) / 2)
    rw [map_mul, map_mul, map_pow, map_commutatorElement])

theorem val_addMap (f : Q →* Q) (x : Baer p Q) : val (addMap f x) = f (val x) := rfl

end Baer

end Baer

end CFSG.RankThree.PartOne.S11d
