module

import CFSG.GroupTheory.SteinbergBKLinearPlaneSL2
public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.RankThree.GroupTheory

open Matrix

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k]

theorem card_dvd_prime_of_isPGroup_GL_two [Finite k] (hk : Nat.card k = p)
    {Q : Subgroup (GL (Fin 2) k)} (hQ : IsPGroup p Q) : Nat.card Q ∣ p := by
  let := Fintype.ofFinite k
  have hq : Fintype.card k = p := by rw [← Nat.card_eq_fintype_card, hk]
  obtain ⟨c, hc⟩ := hQ.exists_card_eq
  have hdvd := Subgroup.card_subgroup_dvd_card Q
  rw [Matrix.card_GL_field, Fin.prod_univ_two, hq, hc] at hdvd
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one] at hdvd
  have hp1 := hp.out.one_lt
  have hfac : (p ^ 2 - 1) * (p ^ 2 - p) = p * ((p ^ 2 - 1) * (p - 1)) := by
    rw [show p ^ 2 - p = p * (p - 1) by
      rw [Nat.mul_sub, mul_one, pow_two]]
    ring
  rw [hfac] at hdvd
  have hcop : Nat.Coprime (p ^ c) ((p ^ 2 - 1) * (p - 1)) := by
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => ?_)
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h1 | h1
    · have h2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
      have h3 := Nat.dvd_sub h2 h1
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at h3
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h3)
    · have h3 := Nat.le_of_dvd (by omega) h1
      omega
  rw [hc]
  exact hcop.dvd_of_dvd_mul_right hdvd

@[expose] def orderThreeSL : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

theorem orderThreeSL_pow_three : (orderThreeSL : Matrix.SpecialLinearGroup (Fin 2) k) ^ 3 = 1 := by
  have h : ((orderThreeSL : Matrix.SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) ^ 3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [orderThreeSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  apply Subtype.ext
  exact (Matrix.SpecialLinearGroup.coe_pow
    (orderThreeSL : Matrix.SpecialLinearGroup (Fin 2) k) 3).trans h

theorem orderThreeSL_ne_one : (orderThreeSL : Matrix.SpecialLinearGroup (Fin 2) k) ≠ 1 := by
  intro h
  have := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) k => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp [orderThreeSL] at this

theorem commutator_eq_bot_of_GL_two [Finite k] (hk : Nat.card k = p) (hp3 : 3 < p)
    {P T : Subgroup (GL (Fin 2) k)} (hP : IsPGroup p P) (hT : IsPGroup 2 T)
    (hPT : P ≤ Subgroup.normalizer (T : Set (GL (Fin 2) k))) : ⁅P, T⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hPT1 : P ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxT⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    obtain ⟨a, ha⟩ := hP ⟨x, hxP⟩
    obtain ⟨b, hb⟩ := hT ⟨x, hxT⟩
    have hoa : orderOf x ∣ p ^ a := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val ha)
    have hob : orderOf x ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hb)
    have hcop : Nat.Coprime (p ^ a) (2 ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    have h1 := Nat.dvd_gcd hoa hob
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hcT : ⁅P, T⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro x hx t ht
    have h1 := (Subgroup.mem_normalizer_iff.mp (hPT hx) t).mp ht
    rw [commutatorElement_def]
    exact T.mul_mem h1 (T.inv_mem ht)
  by_cases hP1 : P = ⊥
  · rw [hP1, Subgroup.commutator_bot_left]
  set H := T ⊔ P with hH
  have hPH : P ≤ H := le_sup_right
  have hPcard : Nat.card P = p := by
    rcases (Nat.dvd_prime hp.out).mp (card_dvd_prime_of_isPGroup_GL_two hk hP) with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hP1
    · exact h1
  by_cases hN : ∃ N : Subgroup H, N.Normal ∧ IsPGroup p N ∧ N ≠ ⊥
  ·
    obtain ⟨N, hNn, hNp, hN1⟩ := hN
    set N' := N.map H.subtype with hN'
    have hN'p : IsPGroup p N' := hNp.map _
    have hHN' : H ≤ Subgroup.normalizer (N' : Set (GL (Fin 2) k)) := by
      have h1 := Subgroup.le_normalizer_map (H := N) H.subtype
      rwa [Subgroup.normalizer_eq_top_iff.mpr hNn, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h1
    have hsup := IsPGroup.to_sup_of_normal_right' hP hN'p (hPH.trans hHN')
    have hsupP : P ⊔ N' = P := by
      refine (Subgroup.eq_of_le_of_card_ge le_sup_left ?_).symm
      rw [hPcard]
      exact Nat.le_of_dvd hp.out.pos (card_dvd_prime_of_isPGroup_GL_two hk hsup)
    have hN'P : N' ≤ P := by
      rw [← hsupP]
      exact le_sup_right
    have hN'1 : N' ≠ ⊥ := fun h => hN1 (by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (x : GL (Fin 2) k) ∈ N' := Subgroup.mem_map_of_mem _ hx
      rw [h, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_bot).mpr (Subtype.ext h1))
    have hN'eq : N' = P := by
      refine Subgroup.eq_of_le_of_card_ge hN'P ?_
      rw [hPcard]
      rcases (Nat.dvd_prime hp.out).mp
          (hPcard ▸ Subgroup.card_dvd_of_le hN'P : Nat.card N' ∣ p) with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) hN'1
      · exact h1.ge
    have hTP : T ≤ Subgroup.normalizer (P : Set (GL (Fin 2) k)) := by
      rw [← hN'eq]
      exact le_sup_left.trans hHN'
    have hcP : ⁅P, T⁆ ≤ P := by
      rw [Subgroup.commutator_le]
      intro x hx t ht
      have h1 := (Subgroup.mem_normalizer_iff.mp (hTP ht) x⁻¹).mp (P.inv_mem hx)
      rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc t]
      exact P.mul_mem hx h1
    rw [eq_bot_iff, ← hPT1]
    exact le_inf hcP hcT
  ·
    exfalso
    push Not at hN
    have hpH : p ∣ Nat.card H := hPcard ▸ Subgroup.card_dvd_of_le hPH
    have hSL := (CFSG.GroupTheory.SteinbergBK.p_reduced_linear_plane_contains_SL2 hk H hpH
      hN).1
    set A := Matrix.SpecialLinearGroup.toGL (orderThreeSL : Matrix.SpecialLinearGroup (Fin 2) k)
    have hAH : A ∈ H := hSL ⟨_, rfl⟩
    have hA3 : orderOf A = 3 := by
      have h1 : A ^ 3 = 1 := by rw [← map_pow, orderThreeSL_pow_three, map_one]
      refine orderOf_eq_prime h1 fun h2 => orderThreeSL_ne_one (k := k) ?_
      exact Matrix.SpecialLinearGroup.toGL_injective (h2.trans (map_one _).symm)
    set Nm := Subgroup.normalizer (T : Set (GL (Fin 2) k))
    have hTNm : T ≤ Nm := Subgroup.le_normalizer
    have hHNm : H ≤ Nm := sup_le hTNm hPT
    set π := QuotientGroup.mk' (T.subgroupOf Nm)
    have hHeq : H.subgroupOf Nm = ((P.subgroupOf Nm).map π).comap π := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', hH, Subgroup.subgroupOf_sup hTNm hPT,
        sup_comm]
    have hAmem : (⟨A, hHNm hAH⟩ : Nm) ∈ ((P.subgroupOf Nm).map π).comap π := by
      rw [← hHeq]
      exact hAH
    have hπp : IsPGroup p ((P.subgroupOf Nm).map π) := (hP.comap_subtype (K := Nm)).map π
    obtain ⟨c, hc⟩ := hπp ⟨_, hAmem⟩
    have hAT : A ^ p ^ c ∈ T := by
      have h1 : π (⟨A, hHNm hAH⟩ ^ p ^ c) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hc
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hcop : (orderOf A).Coprime (p ^ c) := by
      rw [hA3]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp.out).mpr (by omega))
    obtain ⟨b, hb⟩ := hT ⟨_, hAT⟩
    have hob : orderOf (A ^ p ^ c) ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hb)
    rw [hcop.orderOf_pow, hA3] at hob
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hob)
    omega

theorem defining_prime_linear_plane_normalizer_centralizes_two_subgroup (hp3 : 3 < p)
    [Finite k] (hk : Nat.card k = p) {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : Module.finrank k V ≤ 2)
    {P T : Subgroup (LinearMap.GeneralLinearGroup k V)} (hP : IsPGroup p P)
    (hT : IsPGroup 2 T)
    (hPT : P ≤ Subgroup.normalizer (T : Set (LinearMap.GeneralLinearGroup k V))) :
    ⁅P, T⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  generalize hd : Module.finrank k V = d at hV
  set e : LinearMap.GeneralLinearGroup k V ≃* GL (Fin d) k :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv
      (Module.finBasisOfFinrankEq k V hd).equivFun).trans Matrix.GeneralLinearGroup.toLin.symm
  have he : Function.Injective e := e.injective
  have hP' : IsPGroup p (P.map e.toMonoidHom) := hP.map _
  have hT' : IsPGroup 2 (T.map e.toMonoidHom) := hT.map _
  have hPT' : P.map e.toMonoidHom ≤ Subgroup.normalizer
      ((T.map e.toMonoidHom : Subgroup (GL (Fin d) k)) : Set (GL (Fin d) k)) :=
    (Subgroup.map_mono hPT).trans (Subgroup.le_normalizer_map _)
  suffices h : ⁅P.map e.toMonoidHom, T.map e.toMonoidHom⁆ = ⊥ by
    rw [← Subgroup.map_commutator] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ he).mp h
  rcases (show d ≤ 1 ∨ d = 2 by omega) with hd1 | rfl
  ·
    have hP1 : P.map e.toMonoidHom = ⊥ := by
      let := Fintype.ofFinite k
      have hq : Fintype.card k = p := by rw [← Nat.card_eq_fintype_card, hk]
      obtain ⟨c, hc⟩ := hP'.exists_card_eq
      have hdvd := Subgroup.card_subgroup_dvd_card (P.map e.toMonoidHom)
      rw [Matrix.card_GL_field, hq, hc] at hdvd
      have hc0 : c = 0 := by
        by_contra hc0
        have hpd : p ∣ ∏ i : Fin d, (p ^ d - p ^ (i : ℕ)) :=
          (dvd_pow_self p hc0).trans hdvd
        rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
        · simp at hpd
          exact hp.out.one_lt.ne' hpd
        · simp only [Fin.prod_univ_one, Fin.val_zero, pow_zero, pow_one] at hpd
          have h1 := Nat.le_of_dvd (by have := hp.out.one_lt; omega) hpd
          omega
      rw [← Subgroup.card_eq_one, hc, hc0, pow_zero]
    rw [hP1, Subgroup.commutator_bot_left]
  · exact commutator_eq_bot_of_GL_two hk hp3 hP' hT' hPT'

end CFSG.RankThree.GroupTheory
