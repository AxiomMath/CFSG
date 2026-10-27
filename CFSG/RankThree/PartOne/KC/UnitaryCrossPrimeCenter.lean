module

public import CFSG.RankThree.PartOne.KC.MatrixAlgebraCenter
public import CFSG.RankThree.PartOne.KC.MatrixAlgebraFieldProduct
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

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCMatrixAlgebra

section Fix

variable {ι : Type*} [DecidableEq ι] {K : ι → Type*} [∀ i, Field (K i)] {p : ℕ} {A : Type*}
  [Group A]

@[expose] def FixesPrimitive (ψ : RingAut (∀ i, K i)) : Prop :=
  ∀ i : ι, ψ (Pi.single i 1) = Pi.single i 1

theorem ringAut_apply_eq_of_fix (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsPGroup p A)
    (ψ : A →* RingAut (∀ i, K i)) (a : A)
    (hfix : FixesPrimitive (ψ a)) {x : ∀ i, K i} {s : ℕ}
    (hx : x ^ 2 ^ s = 1) : ψ a x = x := by
  obtain ⟨k, hk⟩ := hA a
  funext i
  let τ : K i →* K i := (Pi.evalMonoidHom K i).comp
    ((ψ a).toRingHom.toMonoidHom.comp (MonoidHom.mulSingle K i))
  have hτ : ∀ y : ∀ i, K i, ψ a y i = τ (y i) := fun y =>
    ringAut_apply_coord_of_fix (ψ a) i (hfix i) y
  have hiter : ∀ (n : ℕ) (y : ∀ i, K i), ((ψ a ^ n) y) i = τ^[n] (y i) := by
    intro n y
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', RingAut.mul_apply, hτ, ih, Function.iterate_succ_apply']
  have hpow : ψ a ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hτN : ∀ c : K i, τ^[p ^ k] c = c := by
    intro c
    have := hiter (p ^ k) (Pi.mulSingle i c)
    rw [hpow] at this
    simpa using this.symm
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have hxi : x i ^ 2 ^ s = 1 := by simpa using congrFun hx i
  rw [hτ, monoidHom_apply_eq_of_pow_two_pow_eq_one τ hodd hτN hxi]

variable {m : ι → ℕ} {R : Type*} [Ring R]

@[expose] noncomputable def centerZeta (hm : ∀ i, 0 < m i)
    (e : R ≃+* ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i)) : (∀ i, K i) ≃+* Subring.center R :=
  (scalarCenterEquiv K m hm).trans (Subring.centerCongr e.symm)

@[expose] noncomputable def centerPsi (hm : ∀ i, 0 < m i)
    (e : R ≃+* ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i)) (φ : A →* RingAut R) :
    A →* RingAut (∀ i, K i) where
  toFun b := (centerZeta hm e).trans ((centerRingAut (φ b)).trans (centerZeta hm e).symm)
  map_one' := by
    ext c
    simp
  map_mul' b c := by
    ext d
    simp

theorem apply_eq_of_mem_center_of_psi_fix (hp : p.Prime) (hp2 : p ≠ 2) (hm : ∀ i, 0 < m i)
    (e : R ≃+* ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i)) (hA : IsPGroup p A)
    (φ : A →* RingAut R) (a : A)
    (hfix : FixesPrimitive (centerPsi hm e φ a)) {z : R}
    (hz : z ∈ Subring.center R) {k : ℕ} (hzk : z ^ 2 ^ k = 1) : φ a z = z := by
  set ζ := centerZeta hm e with hζ
  have hc : (ζ.symm ⟨z, hz⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨z, hz⟩ : Subring.center R) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hzk)
    rw [this, map_one]
  have h := ringAut_apply_eq_of_fix hp hp2 hA (centerPsi hm e φ) a hfix hc
  have h2 := congrArg ζ h
  have h3 : centerRingAut (φ a) ⟨z, hz⟩ = ⟨z, hz⟩ := by
    simpa [centerPsi, hζ] using h2
  exact congrArg Subtype.val h3

theorem centerPsi_fix_of_card_lt [Finite ι] (hp : p.Prime) (hι : Nat.card ι < p)
    (hm : ∀ i, 0 < m i) (e : R ≃+* ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i)) (hA : IsPGroup p A)
    (φ : A →* RingAut R) (a : A) : FixesPrimitive (centerPsi hm e φ a) :=
  fun i => ringAut_apply_single_one_of_isPGroup hp hι hA (centerPsi hm e φ) a i

end Fix

end CFSG.RankThree.PartOne.KCUnitaryModel
