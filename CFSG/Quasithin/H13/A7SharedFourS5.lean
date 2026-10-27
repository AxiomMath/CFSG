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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
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

namespace CFSG.Quasithin.H13.A7

open Polynomial Module

theorem aeval_conj_of_mul_eq_one {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {s s' : A} (h : s' * s = 1) (h' : s * s' = 1) (a : A) (p : R[X]) :
    aeval (s * a * s') p = s * aeval a p * s' := by
  have hpow : ∀ n : ℕ, (s * a * s') ^ n = s * a ^ n * s' := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, mul_one, h']
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      calc s * a ^ n * s' * (s * a * s') = s * a ^ n * (s' * s) * a * s' := by
            simp only [mul_assoc]
        _ = s * (a ^ n * a) * s' := by rw [h, mul_one]; simp only [mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial n r =>
    rw [aeval_monomial, aeval_monomial, hpow, Algebra.left_comm s r (a ^ n)]
    simp only [mul_assoc]

variable {k : Type*} [Field k] [Fintype k]

theorem two_eq_zero_of_card_four (hk : Fintype.card k = 4) : (2 : k) = 0 := by
  have h := FiniteField.cast_card_eq_zero k
  rw [hk] at h
  have h2 : (2 : k) * 2 = 0 := by
    rw [← h]
    norm_num
  exact mul_self_eq_zero.1 h2

theorem exists_sq_add_self_add_one_eq_zero (hk : Fintype.card k = 4) :
    ∃ ω : k, ω ^ 2 + ω + 1 = 0 := by
  classical
  obtain ⟨a, ha0, ha1⟩ : ∃ a : k, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := fun a _ => by
      by_cases h : a = 0
      · rw [h]
        exact Finset.mem_insert_self _ _
      · rw [hcon a h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hk] at this
    have h2 : ({0, 1} : Finset k).card ≤ 2 := Finset.card_le_two
    omega
  have h3 : a ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one a ha0
    rwa [hk] at this
  refine ⟨a, ?_⟩
  have h1 : (a - 1) * (a ^ 2 + a + 1) = 0 := by
    have : (a - 1) * (a ^ 2 + a + 1) = a ^ 3 - 1 := by ring
    rw [this, h3, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd (sub_eq_zero.1 h) ha1
  · exact h

theorem eq_one_of_pow_five_eq_one (hk : Fintype.card k = 4) {c : k} (hc : c ^ 5 = 1) :
    c = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  have h3 : c ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [hk] at this
  have h2 : c ^ 2 = 1 := by
    rw [show c ^ 5 = c ^ 3 * c ^ 2 by ring, h3, one_mul] at hc
    exact hc
  rw [show c ^ 3 = c ^ 2 * c by ring, h2, one_mul] at h3
  exact h3

theorem two_le_finrank_ker_quad (hk : Fintype.card k = 4) {W : Type*} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {A : Module.End k W} (hA : A ^ 5 = 1) {b : k}
    (hb : b ≠ 0) (hN : LinearMap.ker (aeval A (X ^ 2 + C b * X + 1)) ≠ ⊥) :
    2 ≤ finrank k (LinearMap.ker (aeval A (X ^ 2 + C b * X + 1))) := by
  set N := LinearMap.ker (aeval A (X ^ 2 + C b * X + 1)) with hNdef
  have h0 : finrank k N ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero]
    exact hN
  have h1 : finrank k N ≠ 1 := by
    intro h1
    obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    have hAv : A v ∈ N := by
      rw [hNdef, LinearMap.mem_ker] at hvN ⊢
      have hcomm : aeval A (X ^ 2 + C b * X + 1) * A = A * aeval A (X ^ 2 + C b * X + 1) :=
        calc aeval A (X ^ 2 + C b * X + 1) * A = aeval A ((X ^ 2 + C b * X + 1) * X) := by
              rw [map_mul, aeval_X]
          _ = aeval A (X * (X ^ 2 + C b * X + 1)) := by rw [mul_comm]
          _ = A * aeval A (X ^ 2 + C b * X + 1) := by rw [map_mul, aeval_X]
      rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, hvN, map_zero]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hvN⟩ : N)
      (fun h => hv0 (congrArg Subtype.val h))).1 h1 ⟨A v, hAv⟩
    have hcv : A v = c • v := (congrArg Subtype.val hc).symm
    have hq : (X ^ 2 + C b * X + 1 : k[X]).eval c = 0 := by
      have := Module.End.aeval_apply_of_mem_apply_eq_smul (p := X ^ 2 + C b * X + 1) hcv
      rw [LinearMap.mem_ker.1 hvN] at this
      exact (smul_eq_zero.1 this.symm).resolve_right hv0
    have h5 : c ^ 5 = 1 := by
      have := Module.End.aeval_apply_of_mem_apply_eq_smul (p := X ^ 5) hcv
      rw [map_pow, aeval_X, hA, Module.End.one_apply, eval_pow, eval_X] at this
      have h' : (c ^ 5 - 1) • v = 0 := by rw [sub_smul, ← this, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hv0)
    have e : (X ^ 2 + C b * X + 1 : k[X]).eval 1 = b + 2 := by
      simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one]
      ring
    rw [eq_one_of_pow_five_eq_one hk h5, e, two_eq_zero_of_card_four hk, add_zero] at hq
    exact hb hq
  omega

theorem five_cycle_conj :
    (finRotate 5) ^ 5 = 1 ∧ finRotate 5 ∈ alternatingGroup (Fin 5) ∧
      (List.formPerm [1, 2, 4, 3] : Equiv.Perm (Fin 5)) * finRotate 5 *
        (List.formPerm [1, 2, 4, 3] : Equiv.Perm (Fin 5))⁻¹ = (finRotate 5) ^ 2 ∧
      finRotate 5 ≠ 1 := by
  refine ⟨by decide, Equiv.Perm.mem_alternatingGroup.2 (by rw [sign_finRotate]; decide),
    by decide, by decide⟩

theorem A7_small_F4_S5_representations_kill_A5 (hk : Fintype.card k = 4) {W : Type*}
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] (hW : finrank k W ≤ 3)
    (β : Equiv.Perm (Fin 5) →* (W ≃ₗ[k] W)) : ∀ a ∈ alternatingGroup (Fin 5), β a = 1 := by
  classical
  obtain ⟨ω, hω⟩ := exists_sq_add_self_add_one_eq_zero hk
  have h2 := two_eq_zero_of_card_four hk
  obtain ⟨hc5, hcA, hsc, hc1⟩ := five_cycle_conj
  set c : Equiv.Perm (Fin 5) := finRotate 5 with hcdef
  set s : Equiv.Perm (Fin 5) := List.formPerm [1, 2, 4, 3] with hsdef
  set ρ : Equiv.Perm (Fin 5) →* Module.End k W :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp β with hρdef
  set A := ρ c with hAdef
  set S := ρ s with hSdef
  set S' := ρ s⁻¹ with hS'def
  have hSS' : S * S' = 1 := by rw [hSdef, hS'def, ← map_mul, mul_inv_cancel, map_one]
  have hS'S : S' * S = 1 := by rw [hSdef, hS'def, ← map_mul, inv_mul_cancel, map_one]
  have hA5 : A ^ 5 = 1 := by rw [hAdef, ← map_pow, hc5, map_one]
  have hSA : S * A * S' = A ^ 2 := by
    rw [hSdef, hAdef, hS'def, ← map_mul, ← map_mul, hsc, map_pow]
  have hAinj : ∀ v : W, A v = 0 → v = 0 := by
    intro v hv
    have h1 : A ^ 4 * A = 1 := by rw [← pow_succ, hA5]
    calc v = (A ^ 4 * A) v := by rw [h1, Module.End.one_apply]
      _ = 0 := by rw [Module.End.mul_apply, hv, map_zero]
  have hS'inj : ∀ v : W, S' v = 0 → v = 0 := by
    intro v hv
    calc v = (S * S') v := by rw [hSS', Module.End.one_apply]
      _ = 0 := by rw [Module.End.mul_apply, hv, map_zero]
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hd : ω - ω ^ 2 ≠ 0 := by
    intro h
    rw [(sub_eq_zero.1 h).symm] at hω
    exact one_ne_zero (by linear_combination hω - ω * h2 : (1 : k) = 0)
  set P2 : k[X] := X ^ 2 + C ω * X + 1 with hP2
  set P3 : k[X] := X ^ 2 + C (ω ^ 2) * X + 1 with hP3
  have h2X : (2 : k[X]) = 0 := by
    rw [show (2 : k[X]) = C 2 from (map_ofNat C 2).symm, h2, C_0]
  have hωX : C ω ^ 2 + C ω + 1 = (0 : k[X]) := by
    rw [← C_pow, ← C_1, ← C_add, ← C_add, hω, C_0]
  have hfac : P2 * P3 * (X - 1) = X ^ 5 - 1 := by
    rw [hP2, hP3, C_pow]
    linear_combination (X ^ 4 + (C ω - 2) * X ^ 3 - (C ω - 2) * X ^ 2 - X) * hωX +
      (-X ^ 4 + 2 * X ^ 3 - 2 * X ^ 2 + X) * h2X
  have hcomp2 : P2.comp (X ^ 2) = P3 ^ 2 := by
    rw [hP2, hP3]
    simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, one_comp]
    rw [C_pow]
    linear_combination (-(C ω * (C ω - 1) * X ^ 2)) * hωX -
      (C ω ^ 2 * X ^ 3 + X ^ 2 + C ω ^ 2 * X) * h2X
  have hcomp3 : P3.comp (X ^ 2) = P2 ^ 2 := by
    rw [hP2, hP3]
    simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, one_comp]
    rw [C_pow]
    linear_combination (-(C ω * X ^ 3 + X ^ 2 + C ω * X)) * h2X
  have hdiff : P2 - P3 = C (ω - ω ^ 2) * X := by
    rw [hP2, hP3, C_sub]
    ring
  have eA : aeval A P2 * aeval A P3 * (A - 1) = 0 := by
    have := congrArg (aeval A) hfac
    rw [map_mul, map_mul, map_sub, map_sub, map_pow, aeval_X, map_one, hA5, sub_self] at this
    exact this
  have e2 : S * aeval A P2 * S' = aeval A P3 ^ 2 := by
    rw [← aeval_conj_of_mul_eq_one hS'S hSS' A P2, hSA, ← map_pow (aeval A) P3 2, ← hcomp2,
      aeval_comp, map_pow (aeval A) X 2, aeval_X]
  have e3 : S * aeval A P3 * S' = aeval A P2 ^ 2 := by
    rw [← aeval_conj_of_mul_eq_one hS'S hSS' A P3, hSA, ← map_pow (aeval A) P2 2, ← hcomp3,
      aeval_comp, map_pow (aeval A) X 2, aeval_X]
  have ed : aeval A P2 - aeval A P3 = algebraMap k (Module.End k W) (ω - ω ^ 2) * A := by
    rw [← map_sub, hdiff, map_mul, aeval_C, aeval_X]
  set N2 := LinearMap.ker (aeval A P2) with hN2
  set N3 := LinearMap.ker (aeval A P3) with hN3
  have hconj : ∀ {Q Q' : k[X]}, S * aeval A Q * S' = aeval A Q' ^ 2 →
      ∀ v ∈ LinearMap.ker (aeval A Q'), S' v ∈ LinearMap.ker (aeval A Q) := by
    intro Q Q' e v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h := LinearMap.congr_fun e v
    rw [Module.End.mul_apply, Module.End.mul_apply, pow_two, Module.End.mul_apply, hv,
      map_zero] at h
    have h' := congrArg S' h
    rwa [← Module.End.mul_apply S' S, hS'S, Module.End.one_apply, map_zero] at h'
  have hne : ∀ {N N' : Submodule k W}, (∀ v ∈ N, S' v ∈ N') → N ≠ ⊥ → N' ≠ ⊥ := by
    intro N N' hNN' hN hN'
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    have := hNN' v hv
    rw [hN', Submodule.mem_bot] at this
    exact hv0 (hS'inj v this)
  have hinf : N2 ⊓ N3 = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv2, hv3⟩ := Submodule.mem_inf.1 hv
    rw [hN2, LinearMap.mem_ker] at hv2
    rw [hN3, LinearMap.mem_ker] at hv3
    have h := LinearMap.congr_fun ed v
    rw [LinearMap.sub_apply, hv2, hv3, sub_zero, Module.End.mul_apply,
      Module.algebraMap_end_apply] at h
    rw [Submodule.mem_bot]
    exact hAinj v ((smul_eq_zero.1 h.symm).resolve_left hd)
  have hboth : N2 ≠ ⊥ → N3 ≠ ⊥ → False := by
    intro h2ne h3ne
    have hr2 : 2 ≤ finrank k N2 := two_le_finrank_ker_quad hk hA5 hω0 h2ne
    have hr3 : 2 ≤ finrank k N3 := two_le_finrank_ker_quad hk hA5 (pow_ne_zero 2 hω0) h3ne
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq N2 N3
    rw [hinf, finrank_bot] at hsum
    have hle := Submodule.finrank_le (N2 ⊔ N3)
    omega
  have hN2bot : N2 = ⊥ := by
    by_contra h
    exact hboth h (hne (hconj e3) h)
  have hN3bot : N3 = ⊥ := by
    by_contra h
    exact hboth (hne (hconj e2) h) h
  have hA1 : ∀ v : W, A v = v := by
    intro v
    have h := LinearMap.congr_fun eA v
    rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
    have h3 : aeval A P3 ((A - 1) v) = 0 := by
      have : aeval A P3 ((A - 1) v) ∈ N2 := LinearMap.mem_ker.2 h
      rwa [hN2bot, Submodule.mem_bot] at this
    have h1 : (A - 1) v = 0 := by
      have : (A - 1) v ∈ N3 := LinearMap.mem_ker.2 h3
      rwa [hN3bot, Submodule.mem_bot] at this
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    exact h1
  have hβc : β c = 1 := by
    ext v
    exact hA1 v
  set K := β.ker.subgroupOf (alternatingGroup (Fin 5)) with hKdef
  have hKn : K.Normal := Subgroup.Normal.subgroupOf inferInstance _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
  · exfalso
    have hcK : (⟨c, hcA⟩ : alternatingGroup (Fin 5)) ∈ K := by
      rw [hKdef, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact hβc
    rw [hK, Subgroup.mem_bot] at hcK
    exact hc1 (congrArg Subtype.val hcK)
  · intro a ha
    have haK : (⟨a, ha⟩ : alternatingGroup (Fin 5)) ∈ K := by
      rw [hK]
      exact Subgroup.mem_top _
    rwa [hKdef, Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at haK

end CFSG.Quasithin.H13.A7
