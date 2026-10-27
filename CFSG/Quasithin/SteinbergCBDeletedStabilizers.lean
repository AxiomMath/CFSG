module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.Quasithin.SteinbergCB

open Equiv Equiv.Perm Subgroup

@[expose] def kleinFiveFun (p : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    Perm (Fin 5) :=
  (swap 0 1 * swap 2 3) ^ (Multiplicative.toAdd p.1).val *
    (swap 0 2 * swap 1 3) ^ (Multiplicative.toAdd p.2).val

theorem kleinFiveFun_mul : ∀ p q : Multiplicative (ZMod 2) × Multiplicative (ZMod 2),
    kleinFiveFun (p * q) = kleinFiveFun p * kleinFiveFun q := by
  decide +kernel

theorem kleinFiveFun_injective : Function.Injective kleinFiveFun := by
  unfold Function.Injective
  decide +kernel

theorem sign_kleinFiveFun : ∀ p : Multiplicative (ZMod 2) × Multiplicative (ZMod 2),
    sign (kleinFiveFun p) = 1 := by
  decide +kernel

@[expose] def fourVecFive : Fin 5 → ZMod 2 := ![1, 1, 1, 1, 0]

@[expose] def twoVecFive : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]

theorem kleinFiveFun_fix : ∀ (p : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (i : Fin 5),
    fourVecFive ((kleinFiveFun p)⁻¹ i) = fourVecFive i := by
  decide +kernel

theorem klein_pow_two : ∀ p : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), p ^ 2 = 1 := by
  decide

@[expose] def kleinFiveHom : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* Perm (Fin 5) :=
  MonoidHom.mk' kleinFiveFun kleinFiveFun_mul

@[expose] def sThreeFiveFun (τ : Perm (Fin 3)) : Perm (Fin 5) :=
  if τ = 1 then 1
  else if τ = swap 0 1 then swap 2 3 * swap 0 1
  else if τ = swap 0 2 then swap 2 4 * swap 0 1
  else if τ = swap 1 2 then swap 3 4 * swap 0 1
  else if τ = swap 0 1 * swap 0 2 then swap 2 3 * swap 2 4
  else swap 2 4 * swap 2 3

theorem sThreeFiveFun_mul : ∀ σ τ : Perm (Fin 3),
    sThreeFiveFun (σ * τ) = sThreeFiveFun σ * sThreeFiveFun τ := by
  decide +kernel

theorem sThreeFiveFun_injective : Function.Injective sThreeFiveFun := by
  unfold Function.Injective
  decide +kernel

theorem sign_sThreeFiveFun : ∀ τ : Perm (Fin 3), sign (sThreeFiveFun τ) = 1 := by
  decide +kernel

theorem sThreeFiveFun_fix : ∀ (τ : Perm (Fin 3)) (i : Fin 5),
    twoVecFive ((sThreeFiveFun τ)⁻¹ i) = twoVecFive i := by
  decide +kernel

@[expose] def sThreeFiveHom : Perm (Fin 3) →* Perm (Fin 5) :=
  MonoidHom.mk' sThreeFiveFun sThreeFiveFun_mul

theorem swap_mul_swap_ne_fin_three :
    (swap 0 1 * swap 0 2 : Perm (Fin 3)) ≠ swap 0 2 * swap 0 1 := by
  decide

theorem exists_perm_evenWeight_five : ∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 →
    ∃ σ : Perm (Fin 5), (∀ i, v (σ i) = 0) ∨ (∀ i, v (σ i) = fourVecFive i) ∨
      ∀ i, v (σ i) = twoVecFive i := by
  decide +kernel

theorem range_permCongrHom_comp_fix {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (e : Fin 5 ≃ Ω)
    {M : Type*} [Group M] (f : M →* Perm (Fin 5)) (hsign : ∀ m, sign (f m) = 1)
    {v₀ : Fin 5 → ZMod 2} (hfix : ∀ m i, v₀ ((f m)⁻¹ i) = v₀ i) {v : Ω → ZMod 2}
    (hv : ∀ i, v (e i) = v₀ i) :
    ((permCongrHom e).toMonoidHom.comp f).range ≤ alternatingGroup Ω ∧
      ∀ g ∈ ((permCongrHom e).toMonoidHom.comp f).range,
        LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ v = v := by
  constructor
  · rintro _ ⟨m, rfl⟩
    rw [mem_alternatingGroup]
    change sign (e.permCongr (f m)) = 1
    rw [sign_permCongr]
    exact hsign m
  · rintro _ ⟨m, rfl⟩
    funext ω
    change v ((e.permCongr (f m))⁻¹ ω) = v ω
    have h1 : (e.permCongr (f m))⁻¹ ω = e ((f m)⁻¹ (e.symm ω)) := by
      rw [Perm.inv_eq_iff_eq, Equiv.permCongr_apply, Equiv.symm_apply_apply, Perm.inv_def,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [h1, hv, hfix, ← hv, Equiv.apply_symm_apply]

theorem not_isCyclic_of_exponent {G : Type*} [Group G] [Finite G] (h2 : Monoid.exponent G ∣ 2)
    (h4 : Nat.card G = 4) : ¬ IsCyclic G := by
  intro hcyc
  rw [IsCyclic.exponent_eq_card, h4] at h2
  norm_num at h2

theorem nq_alternating_five_deleted_module_stabilizers {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 5) (v : Ω → ZMod 2) (hv : ∑ ω, v ω = 0) :
    ((∃ K : Subgroup (Perm Ω), K ≤ alternatingGroup Ω ∧
        (∀ g ∈ K, LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ v = v) ∧
        CFSG.IsElementaryAbelian 2 K ∧ Nat.card K = 4) ∨
      ∃ K : Subgroup (Perm Ω), K ≤ alternatingGroup Ω ∧
        (∀ g ∈ K, LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ v = v) ∧
        Nonempty (K ≃* Perm (Fin 3))) ∧
    ∃ K : Subgroup (Perm Ω), K ≤ alternatingGroup Ω ∧
      (∀ g ∈ K, LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ v = v) ∧ ¬ IsCyclic K ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card K → p = 2 ∨ p = 3 := by
  classical
  let e₁ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hΩ
  obtain ⟨σ, hσ⟩ := exists_perm_evenWeight_five (fun i => v (e₁.symm i))
    (by rw [Equiv.sum_comp e₁.symm v]; exact hv)
  let e : Fin 5 ≃ Ω := σ.trans e₁.symm
  have hklein : ∀ v₀ : Fin 5 → ZMod 2, (∀ p i, v₀ ((kleinFiveFun p)⁻¹ i) = v₀ i) →
      (∀ i, v (e i) = v₀ i) →
      ∃ K : Subgroup (Perm Ω), K ≤ alternatingGroup Ω ∧
        (∀ g ∈ K, LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ v = v) ∧
        CFSG.IsElementaryAbelian 2 K ∧ Nat.card K = 4 := by
    intro v₀ hfix hve
    set f := (permCongrHom e).toMonoidHom.comp kleinFiveHom with hf
    obtain ⟨h1, h2⟩ := range_permCongrHom_comp_fix e kleinFiveHom sign_kleinFiveFun hfix hve
    have hinj : Function.Injective f :=
      (permCongrHom e).injective.comp kleinFiveFun_injective
    have hEA : CFSG.IsElementaryAbelian 2 f.range :=
      { is_comm := ⟨fun a b => by
          obtain ⟨p, hp⟩ := a.2
          obtain ⟨q, hq⟩ := b.2
          apply Subtype.ext
          change (a : Perm Ω) * b = b * a
          rw [← hp, ← hq, ← map_mul, ← map_mul, mul_comm]⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
          obtain ⟨p, hp⟩ := a.2
          apply Subtype.ext
          rw [Subgroup.coe_pow, ← hp, ← map_pow, klein_pow_two, map_one]
          rfl }
    refine ⟨f.range, h1, h2, hEA, ?_⟩
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hsym : (∀ i, v (e i) = twoVecFive i) →
      ∃ K : Subgroup (Perm Ω), K ≤ alternatingGroup Ω ∧
        (∀ g ∈ K, LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ v = v) ∧
        Nonempty (K ≃* Perm (Fin 3)) ∧ ¬ IsCyclic K ∧ Nat.card K = 6 := by
    intro hve
    set f := (permCongrHom e).toMonoidHom.comp sThreeFiveHom with hf
    obtain ⟨h1, h2⟩ := range_permCongrHom_comp_fix e sThreeFiveHom sign_sThreeFiveFun
      sThreeFiveFun_fix hve
    have hinj : Function.Injective f :=
      (permCongrHom e).injective.comp sThreeFiveFun_injective
    refine ⟨f.range, h1, h2, ⟨(MonoidHom.ofInjective hinj).symm⟩, fun hcyc => ?_, ?_⟩
    · have hcomm := (IsCyclic.isMulCommutative (α := f.range)).is_comm.comm
        (MonoidHom.ofInjective hinj (swap 0 1)) (MonoidHom.ofInjective hinj (swap 0 2))
      apply swap_mul_swap_ne_fin_three
      apply (MonoidHom.ofInjective hinj).injective
      rw [map_mul, map_mul]
      exact hcomm
    · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
  have hp4 : ∀ p : ℕ, p.Prime → p ∣ 4 → p = 2 ∨ p = 3 := by
    intro p hp hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p <;> revert hp hdvd <;> decide
  have hp6 : ∀ p : ℕ, p.Prime → p ∣ 6 → p = 2 ∨ p = 3 := by
    intro p hp hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p <;> revert hp hdvd <;> decide
  rcases hσ with h0 | h4 | h2
  · obtain ⟨K, h1, h2, hEA, hcard⟩ := hklein 0 (fun _ _ => rfl) h0
    exact ⟨Or.inl ⟨K, h1, h2, hEA, hcard⟩, K, h1, h2,
      not_isCyclic_of_exponent (@CFSG.IsElementaryAbelian.exponent_dvd_p 2 K _ hEA) hcard,
      fun p hp hdvd => hp4 p hp (hcard ▸ hdvd)⟩
  · obtain ⟨K, h1, h2, hEA, hcard⟩ := hklein fourVecFive kleinFiveFun_fix h4
    exact ⟨Or.inl ⟨K, h1, h2, hEA, hcard⟩, K, h1, h2,
      not_isCyclic_of_exponent (@CFSG.IsElementaryAbelian.exponent_dvd_p 2 K _ hEA) hcard,
      fun p hp hdvd => hp4 p hp (hcard ▸ hdvd)⟩
  · obtain ⟨K, h1, h2', hiso, hcyc, hcard⟩ := hsym h2
    exact ⟨Or.inr ⟨K, h1, h2', hiso⟩, K, h1, h2', hcyc, fun p hp hdvd =>
      hp6 p hp (hcard ▸ hdvd)⟩

end CFSG.Quasithin.SteinbergCB
