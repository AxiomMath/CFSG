module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.S11c.Sec66E6Tw
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTwistedE6Main
public import CFSG.SignalizerFunctorTheorem.NonLocal.TwistedE6Small

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley SteinbergBT CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)

theorem twistedE6_pElement_mem_subfield
    {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) {K : Type} [Field K]
    [Finite K] (k : Subfield K) (hk : Nat.card k = (ℓ ^ d) ^ 2) (σ₀ : k ≃+* k)
    (hσ₀ : ∀ c : k, (σ₀ c : K) = (c : K) ^ ℓ ^ d) (ψ : K ≃+* K) (hψ : ∀ c, ψ c = c ^ ℓ ^ d)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ twistedFixedGroup TwistTag.E6 K ψ.toRingHom) (hxp : ∃ j : ℕ, orderOf x = p ^ j) :
    x ∈ subfieldRootGroupImage TwistTag.E6 k σ₀ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Subtype.finite
  have hσ₀' : ∀ c : k, σ₀.toRingHom c = c ^ ℓ ^ d := fun c =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hσ₀ c)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ (by omega : 1 ≤ d * 2)
    (by rw [hk, ← pow_mul])
  let Ω := AlgebraicClosure k
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  obtain ⟨-, -, hder, ⟨kk, hidx⟩, -⟩ := twisted_E6_full_rational_fixed_group_order hℓ hd k hk
    σ₀.toRingHom hσ₀' Ω (iterateFrobenius Ω ℓ d) (fun c => iterateFrobenius_def ℓ d c)
  let _ : Algebra k K := k.subtype.toAlgebra
  have _ : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let l : K →ₐ[k] Ω := IsAlgClosed.lift
  let ι : K →+* Ω := l.toRingHom
  have hιk : ι.comp k.subtype = algebraMap k Ω := RingHom.ext fun c => l.commutes c
  have hιψ : ι.comp ψ.toRingHom = (iterateFrobenius Ω ℓ d).comp ι := RingHom.ext fun c => by
    change ι (ψ c) = iterateFrobenius Ω ℓ d (ι c)
    rw [hψ, iterateFrobenius_def, map_pow]
  set R := twistedFixedGroup TwistTag.E6 Ω (iterateFrobenius Ω ℓ d) with hR
  set CΩ := (graphFixedRootGroup TwistTag.E6 k σ₀.toRingHom).map
    (baseChangeGL (algebraMap k Ω)) with hCΩ
  obtain ⟨hxC, hxF⟩ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K ψ.toRingHom).1 hx
  have hxR : baseChangeGL ι x ∈ R := by
    refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 Ω _).2
      ⟨baseChangeGL_mem_adjointGroup ι hxC, ?_⟩
    rw [twistHom_baseChangeGL ι hιψ, hxF]
  have hfinR : Finite ↥R := (twisted_E6_full_rational_fixed_group_order hℓ hd k hk σ₀.toRingHom
    hσ₀' Ω (iterateFrobenius Ω ℓ d) (fun c => iterateFrobenius_def ℓ d c)).1
  have hinj : Function.Injective (baseChangeGL ι : ModGL TwistTag.E6.tag K →* _) :=
    baseChangeGL_injective ι
  have hordR : orderOf (⟨baseChangeGL ι x, hxR⟩ : ↥R) = orderOf x := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_injective _ hinj x
  have hnorm : (CΩ.subgroupOf R).Normal := by
    have h1 : CΩ.subgroupOf R = commutator ↥R := by
      rw [← hder, ← Subgroup.map_subtype_commutator]
      exact Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
    rw [h1]
    exact inferInstance
  have hmem : (⟨baseChangeGL ι x, hxR⟩ : ↥R) ∈ CΩ.subgroupOf R :=
    pElement_mem_of_index_dvd_pow hp Nat.prime_three hp3 _ (dvd_of_eq hidx) (by rwa [hordR])
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.mp hmem
  refine ⟨y, hy, hinj ?_⟩
  change baseChangeGL ι (baseChangeGL k.subtype y) = baseChangeGL ι x
  rw [baseChangeGL_baseChangeGL, hιk]
  exact hyx

theorem tagFixedFacts_twistedE6 :
    TagFixedFacts .twistedE6 := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  obtain ⟨hn0, hCEM⟩ := lieModel_twistedE6_iff.mp hM
  subst hn0
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hCEM
  have hK2 : Nat.card K = 2 ^ (2 * (p * f₀)) := by rw [hKcard, ← pow_mul, mul_comm]
  have : Finite (twistedE6RootGroup K σ) := Finite.of_equiv T e.toEquiv
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (twistedE6RootGroup K σ) := MulAut.congr e α with hα'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hKcard σ hσ
  obtain ⟨hηord, hpf, ⟨ψ, hψ⟩, -⟩ :=
    twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two hf K hK2 σ
      hσ Θ hΘ hp (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f', hff'⟩ := hpf
  have hf'f₀ : f' = f₀ := (Nat.eq_of_mul_eq_mul_left hp.pos hff').symm
  have hd : 1 ≤ f' := by omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ε, hε, hzp⟩ := exists_canonical_generator_odd hf hK2 hηord hp hp2 hff'
  have hfix_eq : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub (fieldActor σ ε) := by
    have h1 : ψ * MulAut.congr e α * ψ⁻¹ = fieldActor σ (Θ α') := hψ
    rw [h1]
    apply fixSub_eq_of_zpowers_eq
    have h2 := congrArg (Subgroup.map (fieldActorHom (t := TwistTag.E6) σ)) hzp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hK' : Nat.card K = 2 ^ (2 * f' * p) := by rw [hK2, hff']; ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm]
  obtain ⟨φ, hφ, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * (p * f₀)) hK2
  obtain ⟨κ, hκdef⟩ : ∃ κ, φ ^ (2 * f') = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ 2 ^ (2 * f') := fun c => by
    rw [← hκdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  obtain ⟨T₁, hTdef⟩ : ∃ T₁, φ ^ f' = T₁ := ⟨_, rfl⟩
  have hT : ∀ c, T₁ c = c ^ 2 ^ f' := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  set σ₀ : fixSubfield κ ≃+* fixSubfield κ := fixSubfieldRestrict T₁ κ with hσ₀def
  have hσ₀ : ∀ c : fixSubfield κ, (σ₀ c : K) = (c : K) ^ 2 ^ f' := fun c => by
    rw [hσ₀def, coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hk, hJC, -, hder, hsimple, hnc, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer Nat.prime_two hd
      (by omega : 3 ≤ p) (hp.odd_of_ne_two hp2) K hK' κ hκ σ hσ' σ₀ hσ₀ ε hε
  have : Finite (fixSubfield κ) := Subtype.finite
  set Γ : Subgroup (twistedE6RootGroup K σ) := fixSub (fieldActor σ ε) with hΓ
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ with hJ
  set N : Subgroup (twistedE6RootGroup K σ) := J.subgroupOf (twistedE6RootGroup K σ) with hN
  have hder' : ⁅Γ, Γ⁆ = N := hder
  have hNsub : N.subgroupOf Γ = commutator ↥Γ := by
    rw [← hder', ← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  have hNΓ : N ≤ Γ := hder' ▸ Subgroup.commutator_le_self Γ
  have hNnormal : (N.subgroupOf Γ).Normal := by
    rw [hNsub]
    exact inferInstance
  have hsolv : Group.IsSolvable (↥Γ ⧸ N.subgroupOf Γ) := by
    have : (N.subgroupOf Γ).Normal := hNnormal
    have : CommGroup (↥Γ ⧸ commutator ↥Γ) := inferInstanceAs (CommGroup (Abelianization ↥Γ))
    have : Group.IsSolvable (↥Γ ⧸ commutator ↥Γ) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hNsub.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hNsub.symm).surjective
  have hnc' : ∃ a b : ↥J, a * b ≠ b * a := by
    push Not at hnc
    exact hnc
  have hNperf : Group.IsPerfect ↥N :=
    have : Group.IsPerfect ↥J := isPerfect_of_simple_nonabelian hnc'
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJC).symm.surjective
  have hZk : Subgroup.center (twistedE6RootGroup (fixSubfield κ) σ₀) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 (fixSubfield κ) σ₀
  let eJ : ↥J ≃* twistedE6RootGroup (fixSubfield κ) σ₀ :=
    (Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom)
      (baseChangeGL (fixSubfield κ).subtype) (baseChangeGL_injective _)).symm
  let eN : ↥N ⧸ Subgroup.center ↥N ≃* twistedE6RootGroup (fixSubfield κ) σ₀ :=
    (centerQuotientCongr ((Subgroup.subgroupOfEquivOfLe hJC).trans eJ)).trans
      (centerQuotientEquivSelf hZk)
  have hK0 : Nat.card (fixSubfield κ) = (2 ^ f') ^ 2 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c : fixSubfield κ, σ₀ c = c ^ 2 ^ f' := fun c => Subtype.ext (by
    rw [hσ₀, SubmonoidClass.coe_pow])
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨eDQ⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hd (fixSubfield κ)
      hK0 σ₀ hσ₀'
  have hXmodel : LieModel (twistedE6RootGroup (fixSubfield κ) σ₀) .twistedE6 0 2 f₀ := by
    rw [← hf'f₀]
    exact lieModel_twistedE6_iff.mpr ⟨rfl, ⟨Nat.prime_two, hd, rfl⟩, fixSubfield κ, inferInstance,
      inferInstance, hK0, σ₀.toRingHom, hσ₀', ⟨eDQ.symm⟩⟩
  have hNL : NonLocalized N :=
    SignalizerFunctorTheorem.CatalogBridge.subfieldNonLocalizedTwistedE6_of
      SignalizerFunctorTheorem.NonLocal.subfieldNonLocalizedTwistedE6Small 2 f' p Nat.prime_two hd
      hp (by omega) K hK' κ σ σ₀ hκ hσ' hσ₀
  have hψpow : ∀ c, (σ * ε) c = c ^ 2 ^ f' := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ (2 * f' * p) := by
      rw [← Nat.card_eq_fintype_card, hK']
    have h1 : c ^ (2 ^ (2 * f' * p)) = c := by
      have := FiniteField.pow_card c
      rwa [hcard] at this
    rw [RingAut.mul_apply, hε, hσ', ← pow_mul, show 2 ^ (f' * (p + 1)) * 2 ^ (f' * p) =
      2 ^ (2 * f' * p) * 2 ^ f' by rw [← pow_add, ← pow_add]; congr 1; ring, pow_mul, h1]
  have hPq : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ x ∈ Γ, (∃ k : ℕ, orderOf x = q ^ k) → x ∈ N := by
    intro q hq hq3 x hx ⟨j, hj⟩
    have hxC := graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom x.2
    have hδx : Units.map (entrywiseHom ε.toRingHom) (x : ModGL TwistTag.E6.tag K) = x := by
      have h := congrArg Subtype.val (mem_fixSub.mp hx)
      rwa [coe_fieldActor] at h
    have hxψ : (x : ModGL TwistTag.E6.tag K) ∈
        twistedFixedGroup TwistTag.E6 K (σ * ε).toRingHom := by
      obtain ⟨hxA, hxσ⟩ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
        (graphFixedRootGroup_le _ _ _ x.2)
      refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (σ * ε).toRingHom).2
        ⟨hxA, ?_⟩
      rw [twistHom_apply] at hxσ ⊢
      rw [show (σ * ε).toRingHom = σ.toRingHom.comp ε.toRingHom from RingHom.ext fun _ => rfl,
        ← units_map_entrywiseHom_comp, hδx]
      exact hxσ
    refine Subgroup.mem_subgroupOf.mpr
      (twistedE6_pElement_mem_subfield Nat.prime_two hd (fixSubfield κ) hK0 σ₀ hσ₀ (σ * ε) hψpow
        hq hq3 hxψ ⟨j, ?_⟩)
    rw [Subgroup.orderOf_coe, hj]
  set φ' : T ≃* twistedE6RootGroup K σ := e.trans ψ with hφ'
  have hφα : MulAut.congr φ' α = ψ * MulAut.congr e α * ψ⁻¹ := rfl
  have hΓφ : fixSub (MulAut.congr φ' α) = Γ := by rw [hφα, hfix_eq]
  exact fixedFacts_of_iso_of_eq φ' α hM hf₀ Γ N hΓφ hNΓ hNnormal hNperf hsolv hNL
    (hPq p hp (by omega)) (Or.inl (hPq 2 Nat.prime_two (by norm_num)))
    (Or.inl (lieModel_of_mulEquiv eN.symm hXmodel))

end CFSG.RankThree.PartOne.FieldFix
