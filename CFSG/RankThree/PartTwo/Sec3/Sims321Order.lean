module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open scoped MatrixGroups
open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

theorem exists_orderOf_eq_prime {n : ℕ} (hF : Fintype.card F = 2 ^ n) {r : ℕ} (hr : r.Prime)
    (hr3 : r ∣ 2 ^ (3 * n) - 1) (hrn : ¬ r ∣ 2 ^ n - 1) : ∃ y : SL(3, F), orderOf y = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hunits : Nat.card Fˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
  have hmul := Matrix.card_SL_mul_card_units (n := Fin 3) (R := F)
  have hGL := Matrix.card_GL_field (𝔽 := F) 3
  rw [hF] at hGL
  have hdvd : r ∣ Nat.card (GL (Fin 3) F) := by
    rw [hGL, Fin.prod_univ_three]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    simpa [← pow_mul, mul_comm] using hr3
  rw [← hmul, hunits] at hdvd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
  · exact exists_prime_orderOf_dvd_card' r h
  · exact absurd h hrn

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma exists_fixed_of_prime {V : Type*} [AddCommGroup V] [Module F V] [Finite V]
    {r : ℕ} (hr : r.Prime) (f : V →ₗ[F] V) (hf : f ^ r = 1) (hcard : ¬ r ∣ Nat.card V - 1) :
    ∃ w : V, w ≠ 0 ∧ f w = w := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype V := Fintype.ofFinite V
  let g : Function.End V := fun x => f x
  have h1 : g ^ r ^ 1 = 1 := by
    rw [pow_one]
    funext x
    have := congrArg (fun h : V →ₗ[F] V => h x) hf
    simp only [Module.End.pow_apply, Module.End.one_apply] at this
    exact this
  have hmod := Equiv.Perm.card_fixedPoints_modEq h1
  by_contra hno
  push Not at hno
  have hset : Function.fixedPoints g = {0} := by
    ext x
    simp only [Function.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hx0
      exact hno x hx0 hx
    · rintro rfl
      exact map_zero f
  have hcard1 : Fintype.card (Function.fixedPoints g) = 1 := by
    rw [← Nat.card_eq_fintype_card, hset]
    simp
  rw [hcard1, ← Nat.card_eq_fintype_card] at hmod
  have hpos : 0 < Nat.card V := Nat.card_pos
  exact hcard ((Nat.modEq_iff_dvd' (by omega)).mp hmod.symm)

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma exists_fixed_of_invariant {V : Type*} [AddCommGroup V] [Module F V] [Finite V]
    {r : ℕ} (hr : r.Prime) (f : V →ₗ[F] V) (hf : f ^ r = 1) (W : Submodule F V)
    (hW : ∀ x ∈ W, f x ∈ W) (hcard : ¬ r ∣ Nat.card W - 1) :
    ∃ w ∈ W, w ≠ 0 ∧ f w = w := by
  have hfr : (f.restrict hW) ^ r = 1 := by
    rw [Module.End.pow_restrict r hW]
    ext x
    simp [hf]
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_prime hr (f.restrict hW) hfr hcard
  exact ⟨w, w.2, fun h => hw0 (Subtype.ext h), congrArg Subtype.val hw⟩

omit [DecidableEq F] [CharP F 2] in
private lemma not_dvd_card_sub_one {n : ℕ} (hF : Fintype.card F = 2 ^ n) {r : ℕ}
    (hrn : ¬ r ∣ 2 ^ n - 1) (hr2n : ¬ r ∣ 2 ^ (2 * n) - 1)
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] (S : Submodule F V)
    (h1 : 1 ≤ Module.finrank F S) (h2 : Module.finrank F S ≤ 2) : ¬ r ∣ Nat.card S - 1 := by
  rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card, hF]
  obtain h | h : Module.finrank F S = 1 ∨ Module.finrank F S = 2 := by omega
  · rw [h, pow_one]
    exact hrn
  · rw [h, ← pow_mul, mul_comm]
    exact hr2n

omit [DecidableEq F] [CharP F 2] in
private lemma exists_nilpotent {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    {n : ℕ} (hF : Fintype.card F = 2 ^ n) {r : ℕ} (hr : r.Prime) (hrn : ¬ r ∣ 2 ^ n - 1)
    (hr2n : ¬ r ∣ 2 ^ (2 * n) - 1) (hdim : Module.finrank F V ≤ 3)
    (f : V →ₗ[F] V) (hf : f ^ r = 1) (hfix : ∃ w : V, w ≠ 0 ∧ f w = w) :
    ∃ k : ℕ, (f - 1) ^ k = 0 := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  obtain ⟨k, hk, hk1⟩ := ((LinearMap.eventually_isCompl_ker_pow_range_pow (f - 1)).and
    (Filter.eventually_ge_atTop 1)).exists
  refine ⟨k, ?_⟩
  by_contra hne
  set R := LinearMap.range ((f - 1) ^ k) with hR
  have hcomm : Commute f ((f - 1) ^ k) :=
    ((Commute.refl f).sub_right (Commute.one_right f)).pow_right k
  have hRinv : ∀ x ∈ R, f x ∈ R := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simpa using congrArg (fun g => g x) hcomm.eq.symm⟩
  have hker : ∀ w, f w = w → w ∈ LinearMap.ker ((f - 1) ^ k) := by
    intro w hw
    have h0 : (f - 1) w = 0 := by simp [hw]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk1
    rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, h0, map_zero]
  obtain ⟨w, hw0, hw⟩ := hfix
  have hRtop : R ≠ ⊤ := by
    intro htop
    have hbot : LinearMap.ker ((f - 1) ^ k) = ⊥ := by
      have := hk.inf_eq_bot
      rwa [htop, inf_top_eq] at this
    exact hw0 (by simpa [hbot] using hker w hw)
  have hRbot : R ≠ ⊥ := fun h => hne (LinearMap.range_eq_bot.mp h)
  have hlt : Module.finrank F R < Module.finrank F V := Submodule.finrank_lt hRtop
  have h1 : 1 ≤ Module.finrank F R := Submodule.one_le_finrank_iff.mpr hRbot
  obtain ⟨w', hw'R, hw'0, hw'⟩ := exists_fixed_of_invariant hr f hf R hRinv
    (not_dvd_card_sub_one hF hrn hr2n R h1 (by omega))
  exact hw'0 (hk.disjoint.le_bot ⟨hker w' hw', hw'R⟩)

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma mem_span_of_not_linearIndependent {V : Type*} [AddCommGroup V] [Module F V]
    (f : V →ₗ[F] V) {v : V} (hv : v ≠ 0) (hdep : ¬ LinearIndependent F ![v, f v, f (f v)]) :
    f (f v) ∈ Submodule.span F {v, f v} := by
  by_contra hnot
  apply hdep
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • v + g 1 • f v + g 2 • f (f v) = 0 := by
    simpa [Fin.sum_univ_three] using hg
  have hc : g 2 = 0 := by
    by_contra hc
    apply hnot
    have h : f (f v) = (-(g 2)⁻¹ * g 0) • v + (-(g 2)⁻¹ * g 1) • f v := by
      have h3 : g 2 • f (f v) = -(g 0 • v + g 1 • f v) := eq_neg_of_add_eq_zero_right hg'
      calc f (f v) = (g 2)⁻¹ • (g 2 • f (f v)) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = _ := by rw [h3, smul_neg, smul_add, smul_smul, smul_smul, neg_mul, neg_mul, neg_smul,
          neg_smul, neg_add]
    rw [h]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  rw [hc, zero_smul, add_zero] at hg'
  have hb : g 1 = 0 := by
    by_contra hb
    apply hnot
    have h1 : f v = (-(g 1)⁻¹ * g 0) • v := by
      have h3 : g 1 • f v = -(g 0 • v) := eq_neg_of_add_eq_zero_right hg'
      calc f v = (g 1)⁻¹ • (g 1 • f v) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = _ := by rw [h3, smul_neg, smul_smul, neg_mul, neg_smul]
    have h4 : f (f v) = (-(g 1)⁻¹ * g 0) • f v := by
      conv_lhs => rw [h1]
      rw [map_smul]
    rw [h4]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  rw [hb, zero_smul, add_zero] at hg'
  have ha : g 0 = 0 := by
    rcases smul_eq_zero.mp hg' with h | h
    · exact h
    · exact absurd h hv
  intro i
  fin_cases i <;> simp [ha, hb, hc]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma exists_invariant_of_not_linearIndependent {V : Type*} [AddCommGroup V] [Module F V]
    (f : V →ₗ[F] V) {v : V} (hv : v ≠ 0) (hdep : ¬ LinearIndependent F ![v, f v, f (f v)]) :
    ∃ W : Submodule F V, v ∈ W ∧ 1 ≤ Module.finrank F W ∧ Module.finrank F W ≤ 2 ∧
      ∀ x ∈ W, f x ∈ W := by
  classical
  have h2 := mem_span_of_not_linearIndependent f hv hdep
  have hvW : v ∈ Submodule.span F {v, f v} := Submodule.subset_span (by simp)
  haveI : Module.Finite F (Submodule.span F ({v, f v} : Set V)) :=
    Module.Finite.span_of_finite F (Set.toFinite _)
  refine ⟨Submodule.span F {v, f v}, hvW, ?_, ?_, ?_⟩
  · exact Submodule.one_le_finrank_iff.mpr fun h => hv (by simpa [h] using hvW)
  · refine (finrank_span_le_card _).trans ?_
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact Finset.card_le_two
  · intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [map_add, map_smul, map_smul]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ h2)

theorem linearIndependent_of_orderOf {n : ℕ} (hF : Fintype.card F = 2 ^ n) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrn : ¬ r ∣ 2 ^ n - 1) (hr2n : ¬ r ∣ 2 ^ (2 * n) - 1)
    (y : SL(3, F)) (hy : orderOf y = r) (v : Fin 3 → F) (hv : v ≠ 0) :
    LinearIndependent F
      ![v, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ v,
        (y : Matrix (Fin 3) (Fin 3) F) *ᵥ ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ v)] := by
  classical
  by_contra hdep
  set Y : Matrix (Fin 3) (Fin 3) F := (y : Matrix (Fin 3) (Fin 3) F)
  let f : Module.End F (Fin 3 → F) := Matrix.toLinAlgEquiv' Y
  have hfv : ∀ x, f x = Y *ᵥ x := fun x => Matrix.toLinAlgEquiv'_apply Y x
  have hyr : y ^ r = 1 := hy ▸ pow_orderOf_eq_one y
  have hYr : Y ^ r = 1 := by
    have := congrArg Subtype.val hyr
    rwa [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
  have hf : f ^ r = 1 := by
    show Matrix.toLinAlgEquiv' Y ^ r = 1
    rw [← map_pow, hYr, map_one]
  have hfdep : ¬ LinearIndependent F ![v, f v, f (f v)] := by
    have : ![v, f v, f (f v)] = ![v, Y *ᵥ v, Y *ᵥ (Y *ᵥ v)] := by simp only [hfv]
    rw [this]
    exact hdep
  obtain ⟨W, -, hW1, hW2, hWinv⟩ := exists_invariant_of_not_linearIndependent f hv hfdep
  obtain ⟨w, -, hw0, hw⟩ := exists_fixed_of_invariant hr f hf W hWinv
    (not_dvd_card_sub_one hF hrn hr2n W hW1 hW2)
  obtain ⟨k, hk⟩ := exists_nilpotent hF hr hrn hr2n (by simp) f hf ⟨w, hw0, hw⟩
  have hYk : (Y - 1) ^ k = 0 := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [map_pow, map_sub, map_one, map_zero]
    exact hk
  have hYfrob : Y ^ (2 ^ k) = 1 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := add_pow_char_pow_of_commute (R := Matrix (Fin 3) (Fin 3) F) 2 k
      (Commute.one_right (Y - 1))
    rw [sub_add_cancel] at this
    rw [this, pow_eq_zero_of_le (Nat.lt_two_pow_self).le hYk, one_pow, zero_add]
  have hy2 : y ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hYfrob
  have hrdvd : r ∣ 2 ^ k := hy ▸ orderOf_dvd_of_pow_eq_one hy2
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hrdvd))

end CFSG.RankThree.PartTwo.Sec3.Sims321
