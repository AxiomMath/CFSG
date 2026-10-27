module

public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalCoordinateBases

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section RootFacts

variable {K : Type*} [Field K] {h : K[X]} [Fact (Irreducible h)] {p : ℕ}

theorem root_pow_eq_one (hdvd : h ∣ (X ^ p - 1 : K[X])) : AdjoinRoot.root h ^ p = 1 := by
  have := (AdjoinRoot.mk_eq_zero (f := h) (g := X ^ p - 1)).mpr hdvd
  rwa [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at this

theorem root_ne_one (hm : h.Monic) (hne : h ≠ X - 1) : AdjoinRoot.root h ≠ 1 := by
  intro h1
  have h2 : AdjoinRoot.mk h (X - 1) = 0 := by
    rw [map_sub, AdjoinRoot.mk_X, map_one, h1, sub_self]
  have h3 : h ∣ X - 1 := (AdjoinRoot.mk_eq_zero).mp h2
  have h4 : Irreducible (X - 1 : K[X]) := by
    simpa using Polynomial.irreducible_X_sub_C (1 : K)
  have h5 : (X - 1 : K[X]).Monic := by simpa using monic_X_sub_C (1 : K)
  exact hne (eq_of_monic_of_associated hm h5
    ((Fact.out : Irreducible h).associated_of_dvd h4 h3))

theorem geom_sum_eq_zero_of_pow_eq_one {E : Type*} [Field E] {lam : E} (h1 : lam ≠ 1) {n : ℕ}
    (hn : lam ^ n = 1) : ∑ i ∈ Finset.range n, lam ^ i = 0 := by
  have := geom_sum_mul lam n
  rw [hn, sub_self] at this
  exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h1)

end RootFacts

section Invariant

theorem eq_zero_of_additive_smul_invariant {K E M : Type*} [Field K] [Field E] [AddCommGroup M]
    [Module E M] {p : ℕ} (hp : (p : K) ≠ 0) {lam : E} (h1 : lam ≠ 1) (hlam : lam ^ p = 1)
    (D : M →+ K) (hD : ∀ w, D (lam • w) = D w) (w : M) : D w = 0 := by
  have hpow : ∀ i : ℕ, D (lam ^ i • w) = D w := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, mul_comm, mul_smul, hD, ih]
  have hsum : (∑ i ∈ Finset.range p, lam ^ i) • w = 0 := by
    rw [geom_sum_eq_zero_of_pow_eq_one h1 hlam, zero_smul]
  have := congrArg D hsum
  rw [Finset.sum_smul, map_sum, map_zero] at this
  simp only [hpow, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hp

end Invariant

section Twisted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (x : V ≃ₗ[K] V) (h : K[X])

theorem commute_symm_toLinearMap_toLinearMap :
    Commute x.symm.toLinearMap x.toLinearMap := by
  show x.symm.toLinearMap * x.toLinearMap = x.toLinearMap * x.symm.toLinearMap
  ext v
  simp

@[expose] noncomputable def invRestrict :
    Module.End K (primaryComponent x.toLinearMap (reciprocalPolynomial h)) :=
  x.symm.toLinearMap.restrict fun _ hv =>
    apply_mem_primaryComponent (commute_symm_toLinearMap_toLinearMap x) hv

@[simp] theorem coe_invRestrict (w : primaryComponent x.toLinearMap (reciprocalPolynomial h)) :
    ((invRestrict x h w : primaryComponent x.toLinearMap (reciprocalPolynomial h)) : V) =
      x.symm (w : V) := rfl

theorem coe_pow_invRestrict (n : ℕ) (w : primaryComponent x.toLinearMap (reciprocalPolynomial h)) :
    ((((invRestrict x h) ^ n) w : primaryComponent x.toLinearMap (reciprocalPolynomial h)) : V) =
      (x.symm.toLinearMap ^ n) (w : V) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

theorem coe_aeval_invRestrict (f : K[X])
    (w : primaryComponent x.toLinearMap (reciprocalPolynomial h)) :
    ((aeval (invRestrict x h) f w : primaryComponent x.toLinearMap (reciprocalPolynomial h)) :
      V) = aeval x.symm.toLinearMap f (w : V) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp [aeval_monomial, coe_pow_invRestrict]

theorem aeval_invRestrict_self {h : K[X]} (h0 : h.coeff 0 ≠ 0) :
    aeval (invRestrict x h) h = 0 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [coe_aeval_invRestrict]
  exact (mem_primaryComponent_reciprocalPolynomial h0).mp w.2

@[expose] noncomputable def twistedAction {h : K[X]} (h0 : h.coeff 0 ≠ 0) :
    AdjoinRoot h →ₐ[K] Module.End K (primaryComponent x.toLinearMap (reciprocalPolynomial h)) :=
  Ideal.Quotient.liftₐ (Ideal.span {h}) (aeval (invRestrict x h)) fun f hf => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
    rw [map_mul, aeval_invRestrict_self x h0, zero_mul]

@[expose, instance_reducible] noncomputable def twistedModule {h : K[X]} (h0 : h.coeff 0 ≠ 0) :
    Module (AdjoinRoot h) (primaryComponent x.toLinearMap (reciprocalPolynomial h)) :=
  Module.compHom _ (twistedAction x h0).toRingHom

theorem coe_twistedAction_mk {h : K[X]} (h0 : h.coeff 0 ≠ 0) (f : K[X])
    (w : primaryComponent x.toLinearMap (reciprocalPolynomial h)) :
    ((twistedAction x h0 (AdjoinRoot.mk h f) w :
      primaryComponent x.toLinearMap (reciprocalPolynomial h)) : V) =
      aeval x.symm.toLinearMap f (w : V) :=
  coe_aeval_invRestrict x h f w

theorem coe_twistedAction_root {h : K[X]} (h0 : h.coeff 0 ≠ 0)
    (w : primaryComponent x.toLinearMap (reciprocalPolynomial h)) :
    ((twistedAction x h0 (AdjoinRoot.root h) w :
      primaryComponent x.toLinearMap (reciprocalPolynomial h)) : V) = x.symm (w : V) := by
  rw [AdjoinRoot.root, coe_twistedAction_mk]
  simp

end Twisted

section Paired

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.pairedModel (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) :
    PairedModel Q x h (irreducible_of_mem_primaryFactors hh) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := (mem_primaryFactors.mp hh).2.1
  have : Fact (Irreducible h) := ⟨hirr⟩
  have h0 := hx.coeff_zero_ne hh
  have hh' := hx.reciprocalPolynomial_mem hh
  have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hp0 : p ≠ 0 := fun h0' => hx.cast_ne_zero (by rw [h0']; simp)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0' => by
    rw [h0', zero_pow hp0] at hlamp
    exact zero_ne_one hlamp
  set U₁ := primaryComponent x.toLinearMap h with hU₁
  set U₂ := primaryComponent x.toLinearMap (reciprocalPolynomial h) with hU₂
  let : Module (AdjoinRoot h) U₂ := twistedModule x h0
  have : IsScalarTower K (AdjoinRoot h) U₂ :=
    ⟨fun c e w => by
      change twistedAction x h0 (c • e) w = c • twistedAction x h0 e w
      rw [map_smul]
      rfl⟩
  have : Module.Finite (AdjoinRoot h) U₂ :=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot h) U₂
  let β : U₁ →ₗ[K] U₂ →ₗ[K] K := (QuadraticMap.polarBilin Q).compl₁₂ U₁.subtype U₂.subtype
  have hβ : ∀ (a : AdjoinRoot h) (u : U₁) (w : U₂), β (a • u) w = β u (a • w) := by
    intro a u w
    induction a using AdjoinRoot.induction_on with
    | ih f =>
      change QuadraticMap.polar Q ((AdjoinRoot.mk h f • u : U₁) : V) (w : V) =
        QuadraticMap.polar Q (u : V) ((twistedAction x h0 (AdjoinRoot.mk h f) w : U₂) : V)
      rw [coe_mk_smul_primaryComponent, coe_twistedAction_mk]
      exact hx.polar_aeval f u w
  have hl : ∀ u : U₁, (∀ w : U₂, β u w = 0) → u = 0 := fun u hu =>
    Subtype.ext (hx.eq_zero_of_polar_paired_left hh u.2 fun w hw => hu ⟨w, hw⟩)
  have hr : ∀ w : U₂, (∀ u : U₁, β u w = 0) → w = 0 := fun w hw =>
    Subtype.ext (hx.eq_zero_of_polar_paired_right hh w.2 fun u hu => hw ⟨u, hu⟩)
  obtain ⟨ι₁, ι₂, hι⟩ := exists_paired_trace_coordinates β hβ hl hr
  set m := primaryMultiplicity x.toLinearMap h with hm
  have hm' : m = finrank (AdjoinRoot h) U₁ := rfl
  let ι₁' : (Fin m → AdjoinRoot h) →ₗ[K] V := U₁.subtype ∘ₗ (ι₁.toLinearMap.restrictScalars K)
  let ι₂' : (Fin m → AdjoinRoot h) →ₗ[K] V := U₂.subtype ∘ₗ (ι₂.toLinearMap.restrictScalars K)
  have hι₁'x : ∀ a, ι₁' (AdjoinRoot.root h • a) = x (ι₁' a) := fun a => by
    have := coe_root_smul_primaryComponent x.toLinearMap h (ι₁ a)
    change ((ι₁ (AdjoinRoot.root h • a) : U₁) : V) = x ((ι₁ a : U₁) : V)
    rw [map_smul]
    exact this
  have hι₂x : ∀ a, ι₂' (AdjoinRoot.root h • a) = x.symm (ι₂' a) := fun a => by
    change ((ι₂ (AdjoinRoot.root h • a) : U₂) : V) = x.symm ((ι₂ a : U₂) : V)
    rw [map_smul]
    exact coe_twistedAction_root x h0 (ι₂ a)
  have hxQ : ∀ v, Q (x v) = Q v := fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem v
  have hxQ' : ∀ v, Q (x.symm v) = Q v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (inv_mem hx.mem) v
  have hmemU₁ : ∀ a, ι₁' a ∈ U₁ := fun a => (ι₁ a).2
  have hmemU₂ : ∀ a, ι₂' a ∈ U₂ := fun a => (ι₂ a).2
  have hQ1 : ∀ a, Q (ι₁' a) = 0 := fun a =>
    eq_zero_of_additive_smul_invariant hx.cast_ne_zero hlam1 hlamp
      (AddMonoidHom.mk' (fun a => Q (ι₁' a)) fun a a' => by
        rw [map_add, QuadraticMap.map_add (⇑Q) _ _,
          hx.polar_eq_zero_of_ne hh hne (hmemU₁ a) (hmemU₁ a'), add_zero])
      (fun a => by
        change Q (ι₁' (AdjoinRoot.root h • a)) = Q (ι₁' a)
        rw [hι₁'x, hxQ]) a
  have hQ2 : ∀ a, Q (ι₂' a) = 0 := fun a =>
    eq_zero_of_additive_smul_invariant hx.cast_ne_zero hlam1 hlamp
      (AddMonoidHom.mk' (fun a => Q (ι₂' a)) fun a a' => by
        rw [map_add, QuadraticMap.map_add (⇑Q) _ _,
          hx.polar_reciprocal_eq_zero_of_ne hh hne (hmemU₂ a) (hmemU₂ a'), add_zero])
      (fun a => by
        change Q (ι₂' (AdjoinRoot.root h • a)) = Q (ι₂' a)
        rw [hι₂x, hxQ']) a
  have hdisj : Disjoint U₁ U₂ := by
    have hcop : IsCoprime h (reciprocalPolynomial h) :=
      isCoprime_of_irreducible_monic_ne hirr (irreducible_reciprocalPolynomial hirr h0) hmon
        (monic_reciprocalPolynomial h0) hne
    exact Polynomial.disjoint_ker_aeval_of_isCoprime x.toLinearMap hcop
  have hι₁inj : Function.Injective ι₁' := fun a a' haa =>
    ι₁.injective (Subtype.ext haa)
  have hι₂inj : Function.Injective ι₂' := fun a a' haa =>
    ι₂.injective (Subtype.ext haa)
  have hmult : primaryMultiplicity x.toLinearMap h =
      primaryMultiplicity x.toLinearMap (reciprocalPolynomial h) := by
    have : Fact (Irreducible (reciprocalPolynomial h)) :=
      ⟨irreducible_of_mem_primaryFactors hh'⟩
    have h1 := finrank_primaryComponent x.toLinearMap h
    have h2 := finrank_primaryComponent x.toLinearMap (reciprocalPolynomial h)
    have h3 : finrank K U₁ = finrank K U₂ := by
      rw [← (ι₁.restrictScalars K).finrank_eq, ← (ι₂.restrictScalars K).finrank_eq]
    rw [h1, h2, natDegree_reciprocalPolynomial h0] at h3
    exact Nat.eq_of_mul_eq_mul_left (Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible hirr)) h3
  refine ⟨(natDegree_reciprocalPolynomial h0).symm, hmult, ι₁'.coprod ι₂', ?_, ?_, ?_, ?_⟩
  ·
    intro w w' hww
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hww
    have h1 : ι₁' (w.1 - w'.1) = -(ι₂' (w.2 - w'.2)) := by
      rw [map_sub, map_sub, neg_sub, sub_eq_sub_iff_add_eq_add, hww]
      exact add_comm _ _
    have h2 : ι₁' (w.1 - w'.1) ∈ U₁ ⊓ U₂ :=
      ⟨hmemU₁ _, by rw [h1]; exact U₂.neg_mem (hmemU₂ _)⟩
    rw [hdisj.eq_bot] at h2
    have h3 : ι₁' (w.1 - w'.1) = 0 := (Submodule.mem_bot K).mp h2
    have h4 : ι₂' (w.2 - w'.2) = 0 := by rw [h3] at h1; exact neg_eq_zero.mp h1.symm
    exact Prod.ext (sub_eq_zero.mp (hι₁inj (by rw [h3, map_zero])))
      (sub_eq_zero.mp (hι₂inj (by rw [h4, map_zero])))
  ·
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro _ ⟨w, rfl⟩
      rw [LinearMap.coprod_apply]
      exact Submodule.add_mem_sup (hmemU₁ _) (hmemU₂ _)
    · intro u hu
      refine ⟨(ι₁.symm ⟨u, hu⟩, 0), ?_⟩
      simp [ι₁']
    · intro u hu
      refine ⟨(0, ι₂.symm ⟨u, hu⟩), ?_⟩
      simp [ι₂']
  · intro a b
    have hpolar : QuadraticMap.polar Q (ι₁' a) (ι₂' b) =
        Algebra.trace K (AdjoinRoot h) (∑ i, a i * b i) := hι a b
    simp only [LinearMap.coprod_apply]
    rw [QuadraticMap.map_add (⇑Q) _ _, hQ1, hQ2, hpolar]
    ring
  · intro a b
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, map_add, hι₁'x]
    have : ι₂' b = x.symm (ι₂' ((AdjoinRoot.root h)⁻¹ • b)) := by
      rw [← hι₂x, smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    rw [this, x.apply_symm_apply]

end Paired

end CFSG.RankThree.PartOne.KCOrthogonal
