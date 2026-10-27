module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.Permutation.FiveTransitive.Degree24ThirteenFiniteChecks
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem subgroup_card_twenty_five_pow_five_eq_one
    (X : Type) [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 24)
    (R : Subgroup (Equiv.Perm X))
    (hRcard : Nat.card R = 25)
    (r : R) :
    r ^ 5 = 1 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply Subtype.ext
  change ((r : Equiv.Perm X) ^ 5) = 1
  rw [Equiv.Perm.pow_prime_eq_one_iff]
  intro c hc
  have horderDvd :
      orderOf (r : Equiv.Perm X) ∣ 25 := by
    rw [Subgroup.orderOf_coe, ← hRcard,
      Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  have hcDvd : c ∣ 25 :=
    (Equiv.Perm.dvd_of_mem_cycleType hc).trans
      horderDvd
  have hcTwo : 2 ≤ c :=
    Equiv.Perm.two_le_of_mem_cycleType hc
  have hcLe : c ≤ 24 := by
    calc
      c ≤ (r : Equiv.Perm X).cycleType.sum :=
        Multiset.le_sum_of_mem hc
      _ ≤ Fintype.card X :=
        Equiv.Perm.sum_cycleType_le _
      _ = 24 := hcard
  interval_cases c <;> norm_num at hcDvd
  rfl

theorem mulAut_card_eq_four_hundred_eighty_of_subgroup_card_twenty_five
    (X : Type) [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 24)
    (R : Subgroup (Equiv.Perm X))
    (hRcard : Nat.card R = 25) :
    Nat.card (MulAut R) = 480 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : CommGroup R :=
    IsPGroup.commGroupOfCardEqPrimeSq
      (p := 5) (by
        rw [hRcard]
        norm_num)
  let A := Additive R
  have hAcard : Nat.card A = 25 := by
    change Nat.card (Additive R) = 25
    rw [Nat.card_congr
      (Additive.toMul : Additive R ≃ R), hRcard]
  have hfive (a : A) : 5 • a = 0 := by
    change ((a.toMul : R) ^ 5 : R) = 1
    exact
      subgroup_card_twenty_five_pow_five_eq_one
        X hcard R hRcard a.toMul
  letI : Module (ZMod 5) A :=
    AddCommGroup.zmodModule hfive
  have hpow :=
    Module.natCard_eq_pow_finrank
      (K := ZMod 5) (V := A)
  rw [Nat.card_zmod, hAcard] at hpow
  have hfinrankLe :
      Module.finrank (ZMod 5) A ≤ 2 := by
    by_contra hnot
    have hthree :
        3 ≤ Module.finrank (ZMod 5) A := by
      omega
    have hpows :
        5 ^ 3 ≤
          5 ^ Module.finrank (ZMod 5) A :=
      pow_le_pow_right' (by norm_num) hthree
    omega
  have hfinrank :
      Module.finrank (ZMod 5) A = 2 := by
    interval_cases Module.finrank (ZMod 5) A <;>
      norm_num at hpow
    rfl
  let V := Fin 2 → ZMod 5
  have hVfinrank :
      Module.finrank (ZMod 5) V = 2 := by
    rw [Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  let e : A ≃ₗ[ZMod 5] V :=
    (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (hfinrank.trans hVfinrank.symm)).some
  let addLinearEquiv :
      AddAut A ≃ (A ≃ₗ[ZMod 5] A) := {
    toFun := fun f =>
      f.toLinearEquiv (ZMod.map_smul f)
    invFun := fun f => f.toAddEquiv
    left_inv := fun f => rfl
    right_inv := fun f => rfl }
  let b : Module.Basis (Fin 2) (ZMod 5) A :=
    (Pi.basisFun (ZMod 5) (Fin 2)).map e.symm
  calc
    Nat.card (MulAut R) =
        Nat.card (Additive (MulAut R)) :=
      (Nat.card_congr
        (Additive.toMul :
          Additive (MulAut R) ≃ MulAut R)).symm
    _ = Nat.card (AddAut A) := by
      simpa only [A] using
        (Nat.card_congr
          (AddAutAdditive R).toEquiv).symm
    _ = Nat.card (A ≃ₗ[ZMod 5] A) :=
      Nat.card_congr addLinearEquiv
    _ = Nat.card
        (LinearMap.GeneralLinearGroup (ZMod 5) A) :=
      Nat.card_congr
        (LinearMap.GeneralLinearGroup.generalLinearEquiv
          (ZMod 5) A).toEquiv.symm
    _ = Nat.card
        (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) :=
      Nat.card_congr
        (Matrix.GeneralLinearGroup.toLin' b).toEquiv.symm
    _ = 480 := by
      rw [Matrix.card_GL_field]
      decide

end FiveTransitive.Degree24

end CFSG
