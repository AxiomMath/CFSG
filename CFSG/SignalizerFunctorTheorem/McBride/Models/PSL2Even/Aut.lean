module

import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic
import CFSG.Walter.PSL2Facts.Even
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
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
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
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

open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Even

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo

theorem exists_aut {p : ℕ} (hp : p.Prime) :
    ∃ f : MulAut PSL(2, GaloisField 2 p), orderOf f = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hGal : Nat.card (GaloisField 2 p ≃+* GaloisField 2 p) = p :=
    natCard_ringEquiv_galoisField 2 hp.ne_zero
  have : Finite (GaloisField 2 p ≃+* GaloisField 2 p) :=
    Nat.finite_of_card_ne_zero (by rw [hGal]; exact hp.ne_zero)
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' p (by rw [hGal])
  refine ⟨psl2FieldAut (GaloisField 2 p) σ, ?_⟩
  rw [orderOf_injective (psl2FieldAut (GaloisField 2 p))
    (psl2FieldAut_injective (GaloisField 2 p)) σ, hσ]

theorem toPGL_surjective (K : Type*) [Field K] [Finite K] [CharP K 2] :
    Function.Surjective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, K) →* PGL(2, K)) := by
  have : Finite PGL(2, K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) K → PGL(2, K))
      Matrix.ProjGenLinGroup.mk_surjective
  have hcard : Nat.card PGL(2, K) ≤ Nat.card PSL(2, K) := by
    rw [card_pgl2_eq_mul K, CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.card_bot, mul_one]
  exact (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.bijective_of_nat_card_le hcard).2

theorem exists_conj_of_coprime_orderOf {p : ℕ} (hp : p.Prime)
    (g : MulAut PSL(2, GaloisField 2 p)) (hg : Nat.Coprime p (orderOf g)) :
    ∃ x : PSL(2, GaloisField 2 p), g = MulAut.conj x := by
  classical
  set K := GaloisField 2 p
  let e := semilinearEquivAut K
  set y := e.symm g with hydef
  have hGal : Nat.card (K ≃+* K) = p := natCard_ringEquiv_galoisField 2 hp.ne_zero
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hGal]; exact hp.ne_zero)
  have hπ : (SemidirectProduct.rightHom y : K ≃+* K) = 1 := by
    have hdvd1 : orderOf (SemidirectProduct.rightHom y) ∣ orderOf g := by
      rw [← MulEquiv.orderOf_eq e.symm g]
      exact orderOf_map_dvd _ _
    have hdvd2 : orderOf (SemidirectProduct.rightHom y) ∣ p :=
      (orderOf_dvd_natCard _).trans (dvd_of_eq hGal)
    have h := Nat.dvd_gcd hdvd2 hdvd1
    rw [hg.gcd_eq_one] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
  have hy : y = SemidirectProduct.inl y.left := SemidirectProduct.ext rfl (by simpa using hπ)
  obtain ⟨x, hx⟩ := toPGL_surjective K y.left
  refine ⟨x, ?_⟩
  calc g = e y := (e.apply_symm_apply g).symm
    _ = e (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x)) := by
        rw [hy, hx]
    _ = MulAut.conj x := by
        change semilinearAction K _ = _
        rw [semilinearAction_inl, pglAction_toPGL]

theorem exists_pow_mem_range_conj {p : ℕ} (hp : p.Prime) (g : MulAut PSL(2, GaloisField 2 p)) :
    ∃ a : ℕ, g ^ (p ^ a) ∈
      (MulAut.conj : PSL(2, GaloisField 2 p) →* MulAut PSL(2, GaloisField 2 p)).range := by
  obtain ⟨a, m, hm, hg⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  refine ⟨a, ?_⟩
  have hdvd : p ^ a ∣ orderOf g := ⟨m, hg⟩
  have hord : orderOf (g ^ (p ^ a)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a hp.ne_zero) hdvd, hg,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos a)]
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  obtain ⟨x, hx⟩ := exists_conj_of_coprime_orderOf hp (g ^ (p ^ a)) (by rw [hord]; exact hcop)
  exact ⟨x, hx.symm⟩

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Even
