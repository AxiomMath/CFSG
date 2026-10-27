module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo

theorem natCard_ringEquiv_galoisField (ℓ : ℕ) [Fact ℓ.Prime] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (GaloisField ℓ n ≃+* GaloisField ℓ n) = n := by
  let e : (GaloisField ℓ n ≃+* GaloisField ℓ n) ≃
      (GaloisField ℓ n ≃ₐ[ZMod ℓ] GaloisField ℓ n) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun x => by
        have h : (σ.toRingHom.comp (algebraMap (ZMod ℓ) (GaloisField ℓ n)) :
            ZMod ℓ →+* GaloisField ℓ n) = algebraMap (ZMod ℓ) (GaloisField ℓ n) :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
      invFun := fun σ => σ.toRingEquiv
      left_inv := fun σ => by ext x; rfl
      right_inv := fun σ => by ext x; rfl }
  rw [Nat.card_congr e, IsGalois.card_aut_eq_finrank (ZMod ℓ) (GaloisField ℓ n),
    GaloisField.finrank ℓ hn]

section

variable (K : Type*) [Field K]

theorem card_center_sl2_le_two :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) ≤ 2 := by
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (i := (0 : Fin 2)) (R := K)).toEquiv]
  exact card_rootsOfUnity K 2

theorem card_pgl2_eq_mul [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) *
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  rw [CFSG.GorensteinWalter.pgl2_card_formula, ← CFSG.GorensteinWalter.sl2_card_formula,
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))]

theorem two_dvd_natCard_psl2 [Finite K] :
    2 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  obtain ⟨w, hw0⟩ : ∃ w : Matrix.SpecialLinearGroup (Fin 2) K,
      (w : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] :=
    ⟨⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, rfl⟩
  have hw2 : w ^ 2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, hw0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply]
  have hw : w ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    rintro ⟨r, -, hr⟩
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hr
    simp [hw0, Matrix.scalar_apply] at this
  have h2 : (QuotientGroup.mk w : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hw2
  have h1 : (QuotientGroup.mk w : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_dvd_natCard (QuotientGroup.mk w : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
  rwa [orderOf_eq_prime h2 h1] at h

theorem odd_of_coprime_natCard_psl2 [Finite K] {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) :
    Odd p := by
  rcases hp.eq_two_or_odd' with rfl | h
  · exact absurd (Nat.Coprime.coprime_dvd_right (two_dvd_natCard_psl2 K) hcop) (by decide)
  · exact h

theorem coprime_natCard_pgl2 [Finite K] {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) :
    Nat.Coprime p (Nat.card (Matrix.ProjGenLinGroup (Fin 2) K)) := by
  rw [card_pgl2_eq_mul]
  refine hcop.mul_right ?_
  have hodd := odd_of_coprime_natCard_psl2 K hp hcop
  have hle := card_center_sl2_le_two K
  have hpos : 0 < Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) :=
    Nat.card_pos
  have hdvd : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) ∣ 2 := by
    interval_cases h : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    · exact one_dvd _
    · exact dvd_refl _
  refine Nat.Coprime.coprime_dvd_right hdvd ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h2
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  subst this
  exact (by decide : ¬ Odd 2) hodd

end

end CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo
