module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6Noninner
import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree

public section

open CFSG.Open (signalizerFixedSubgroup signalizerNearPSolvable)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.FieldGraphFieldPointwise
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)
open CFSG.RankThree.Chevalley (exists_mulEquiv_graphFixedRootGroup_of_twisted_prime
  Chevalley_exceptional_models_order_divisible_by_three subfieldRootGroupImage
  exists_fieldActor_eq_of_fix_regular_E6
  twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
  twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem twistedE6_zpowers_of_fixes
    {ℓ d m : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hm : 3 ≤ m)
    (hmodd : Odd m) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * d * m))
    (κ : K ≃+* K) (hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ ℓ ^ (d * m)) (σ₀ : fixSubfield κ ≃+* fixSubfield κ)
    (hσ₀ : ∀ c, (σ₀ c : K) = (c : K) ^ ℓ ^ d) (ε : K ≃+* K)
    (hε : ∀ c, ε c = c ^ ℓ ^ (d * (m + 1))) :
    ∀ β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      (∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (x : ModGL TwistTag.E6.tag K) ∈ subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ →
          β x = x) →
        β ∈ Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ ε) := by
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  set ι : fixSubfield κ →+* K := (fixSubfield κ).subtype with hιdef
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀
  set δ := fieldActor (t := TwistTag.E6) σ ε
  have : Finite (fixSubfield κ) := Subtype.finite
  have hdm : 1 ≤ d * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2dm : 1 ≤ 2 * d * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨j, hj⟩ := hmodd
  obtain ⟨fr, hfr, hord, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ h2dm hK
  have hfr1 : fr ^ (2 * d * m) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one fr
  have hσfr : σ = fr ^ (d * m) := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr]
  have hκfr : κ = fr ^ (2 * d) := RingEquiv.ext fun c => by
    rw [hκ, ringAut_pow_apply_of_frobenius hfr]
  have hεfr : ε = fr ^ (d * (m + 1)) := RingEquiv.ext fun c => by
    rw [hε, ringAut_pow_apply_of_frobenius hfr]
  have hκε : κ = ε ^ 2 := by
    rw [hκfr, hεfr, ← pow_mul, show d * (m + 1) * 2 = 2 * d * m + 2 * d by ring, pow_add, hfr1,
      one_mul]
  have hσκ : σ = fr ^ d * κ ^ j := by
    rw [hσfr, hκfr, ← pow_mul, ← pow_add, hj, show d * (2 * j + 1) = d + 2 * d * j by ring]
  have hfrd : ∀ c, (fr ^ d) c = c ^ ℓ ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hstab : ∀ (φ : K ≃+* K) (c : K), φ c = c → ∀ n : ℕ, (φ ^ n) c = c := by
    intro φ c h n
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, h]
  have hκK₀ : ∀ c, ε c = c → κ c = c := fun c hc => by
    rw [hκε]
    exact hstab ε c hc 2
  have hσK₀ : ∀ c, κ c = c → σ c = c ^ ℓ ^ d := fun c hc => by
    rw [hσκ, RingAut.mul_apply, hstab κ c hc j, hfrd]
  have hσ₀σ₀ : ∀ c : fixSubfield κ, σ₀ (σ₀ c) = c := fun c => Subtype.ext (by
    rw [hσ₀, hσ₀, ← pow_mul, ← pow_add, show d + d = 2 * d by ring, ← hκ]
    exact c.2)
  have hσι : ∀ c : fixSubfield κ, σ.toRingHom (ι c) = ι (σ₀.toRingHom c) := fun c => by
    change σ c = (σ₀ c : K)
    rw [hσ₀, hσK₀ c c.2]
  have hJC : J ≤ C := map_baseChangeGL_graphFixedRootGroup_le (σ := σ₀.toRingHom)
    (Fr := σ.toRingHom) (ι := ι) σ₀.surjective hσι
  have hK' : Nat.card K = (ℓ ^ (d * m)) ^ 2 := by
    rw [hK, ← pow_mul, show d * m * 2 = 2 * d * m by ring]
  have hregι : (regularElt K : ModGL TwistTag.E6.tag K) =
      baseChangeGL ι (regularElt (fixSubfield κ) : ModGL TwistTag.E6.tag (fixSubfield κ)) := by
    rw [coe_regularElt (K := K), coe_regularElt (K := fixSubfield κ), map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    rw [Function.comp_apply, baseChangeGL_xUnit, map_one]
  intro β hβ
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
  obtain ⟨w₁, hw₁, h₁⟩ := TwistTag.exists_reversesSigns_mem_relWeylTwist TwistTag.E6
  rw [h₁.eq (reversesSigns_of_forall_length_le hw₀)] at hw₁
  have hn₀J : canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀ ∈ J :=
    ⟨_, canonicalRep_mem_graphFixedRootGroup (K := fixSubfield κ) (σ := σ₀.toRingHom) hw₁,
      baseChangeGL_canonicalRep ι w₀⟩
  have hu₀J : (regularElt K : ModGL TwistTag.E6.tag K) ∈ J :=
    ⟨_, regularElt_mem_graphFixedRootGroup (K := fixSubfield κ) σ₀.toRingHom, hregι.symm⟩
  obtain ⟨η, rfl⟩ := exists_fieldActor_eq_of_fix_regular_E6 hℓ hdm hK' σ hσ hw₀
    (n₀ := ⟨_, hJC hn₀J⟩) (u₀ := ⟨_, hJC hu₀J⟩) rfl rfl (hβ _ hu₀J)
    (hβ _ (mul_mem (mul_mem hn₀J hu₀J) (inv_mem hn₀J)))
  have hηK₀ : ∀ c, ε c = c → η c = c := by
    intro c hc
    have hck : κ c = c := hκK₀ c hc
    have hc₀ : (⟨c, hck⟩ : fixSubfield κ) ∈
        orbitField TwistTag.E6 (fixSubfield κ) σ₀.toRingHom ⟨0, by decide⟩ := by
      rw [mem_orbitField, show (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 by decide, pow_two]
      exact hσ₀σ₀ _
    have hy := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ₀.toRingHom ⟨0, by decide⟩ ⟨_, hc₀⟩)
    have hyJ : baseChangeGL ι
        (orbitX TwistTag.E6 (fixSubfield κ) σ₀.toRingHom ⟨0, by decide⟩ ⟨_, hc₀⟩ :
          ModGL TwistTag.E6.tag (fixSubfield κ)) ∈ J := ⟨_, hy, rfl⟩
    have h1 : Units.map (entrywiseHom η.toRingHom) (baseChangeGL ι
        (orbitX TwistTag.E6 (fixSubfield κ) σ₀.toRingHom ⟨0, by decide⟩ ⟨_, hc₀⟩ :
          ModGL TwistTag.E6.tag (fixSubfield κ))) = baseChangeGL ι
        (orbitX TwistTag.E6 (fixSubfield κ) σ₀.toRingHom ⟨0, by decide⟩ ⟨_, hc₀⟩ :
          ModGL TwistTag.E6.tag (fixSubfield κ)) :=
      congrArg Subtype.val (hβ ⟨_, hJC hyJ⟩ hyJ)
    simp only [coe_orbitX_zero, map_mul, baseChangeGL_xUnit, units_map_entrywiseHom_xUnit] at h1
    have h2 := congrArg (rootCoord (single_pos (τ := TwistTag.E6.tag) ⟨0, by decide⟩)) h1
    simp only [rootCoord_single_xUnit_mul_xUnit] at h2
    simpa [hιdef] using h2
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1
    (CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hηK₀)
  exact Subgroup.mem_zpowers_iff.2
    ⟨n, (map_zpow (fieldActorHom (t := TwistTag.E6) σ) ε n).symm⟩

theorem fieldClauses_twistedE6
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp3 : 3 < p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hsC : IsSimpleGroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hnC : ∃ a b : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, a * b ≠ b * a)
    (hpC : ¬ p ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hNL : SubfieldNonLocalizedTwistedE6) :
    FieldClauses p (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  rintro ⟨α, hα⟩
  obtain ⟨-, ⟨d, hd⟩, -⟩ := twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial
    hℓ hf K hK2f σ hσ Θ hΘ hp hp3 ⊤ le_top ⟨α, Subgroup.mem_top α⟩
    (not_mem_inner_range_of_orderOf hpC hα) (by rw [Subgroup.orderOf_mk, hα])
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ
    (by omega : 1 ≤ 2 * f) hK2f
  obtain ⟨T, hT⟩ : ∃ T : K ≃+* K, ∀ c, T c = c ^ ℓ ^ d :=
    ⟨fr ^ d, fun c => ringAut_pow_apply_of_frobenius hfr d c⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  obtain ⟨ε, hε⟩ : ∃ ε : K ≃+* K, ∀ c, ε c = c ^ ℓ ^ (d * (p + 1)) :=
    ⟨fr ^ (d * (p + 1)), fun c => ringAut_pow_apply_of_frobenius hfr (d * (p + 1)) c⟩
  have hKdp : Nat.card K = ℓ ^ (2 * d * p) := by rw [hK2f, ← hdp, mul_assoc]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hdp, hσ]
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨-, -, hJC, hδord, hder, hsimpleJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd1
      (by omega : 3 ≤ p) hpodd K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  have hfixpow := twistedE6_zpowers_of_fixes hℓ hd1 (by omega : 3 ≤ p) hpodd K hKdp κ hκ σ hσdp
    (fixSubfieldRestrict T κ) hσ₀ ε hε
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ)
  set δ := fieldActor (t := TwistTag.E6) σ ε
  set Γ := MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id C)
  have hJΓ : J.subgroupOf C ≤ Γ := by
    rw [← hder]
    exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)) (Γ.inv_mem hb)
  have hJnorm : ((J.subgroupOf C).subgroupOf Γ).Normal := by
    rw [← hder]
    have h := Subgroup.normal_subgroupOf_commutator_sup Γ Γ
    rwa [sup_idem] at h
  have eJC : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  have hJs : IsSimpleGroup (J.subgroupOf C) := eJC.isSimpleGroup
  have hJn : ∃ x y : J.subgroupOf C, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  refine ⟨δ, hδord, fixedClauses_of_simple_normal_stabilizer hp hsC hnC hpC hδord hJΓ hJnorm hJs
    hJn (fun t => Iff.rfl) (fun g hg => hfixpow g fun x hx => hg x (Subgroup.mem_subgroupOf.2 hx))
    fun _ => NonLocalized.mono hJΓ (hNL ℓ d p hℓ hd1 hp hp3 K hKdp κ σ (fixSubfieldRestrict T κ)
      hκ hσdp hσ₀)⟩

theorem fieldClauses_chevalleyTwistedE6
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .twistedE6 ℓ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedTwistedE6) :
    FieldClauses p T := by
  have hp3 : 3 < p := by
    have h3 := Chevalley_exceptional_models_order_divisible_by_three T .twistedE6 ℓ f hm
    have hp3 : p ≠ 3 := fun h => hpT (h ▸ h3)
    have := hp.two_le
    omega
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, σ₀, hK, hσ₀, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hadm.1 hadm.2.1 hmod
  have hbij : Function.Bijective σ₀ := ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  set σ : K ≃+* K := RingEquiv.ofBijective σ₀ hbij with hσdef
  have hσ : ∀ c, σ c = c ^ (ℓ ^ f) := hσ₀
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := hK
  let e' : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≃* T := e
  have : IsSimpleGroup T := hs
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    Finite.of_equiv T e'.symm.toEquiv
  have hsC : IsSimpleGroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := e'.isSimpleGroup
  have hnC : ∃ a b : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    refine ⟨e'.symm a, e'.symm b, fun h => hab (e'.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hpC : ¬ p ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
    rwa [Nat.card_congr e'.toEquiv]
  exact FieldClauses.of_mulEquiv e'
    (fieldClauses_twistedE6 hadm.1 hadm.2.1 hp hp3 K hK2 σ hσ hsC hnC hpC hNL)

theorem nearOrField_chevalleyTwistedE6
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .twistedE6 ℓ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedTwistedE6) :
    signalizerNearPSolvable p T ∨ FieldClauses p T :=
  Or.inr (fieldClauses_chevalleyTwistedE6 hs hn hm hp hp2 hpT hNL)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
