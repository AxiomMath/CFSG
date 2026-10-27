module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldGlue
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal
public import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed
import CFSG.GroupTheory.ABGDGroups.LinearStructure

public section

open CFSG.Open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

section Compat

variable (K : Type) [Field K] [Finite K]

theorem coordinatePSLAction_psl2FieldAut (σ : K ≃+* K) (x : PSL2 K) :
    coordinatePSLAction K (psl2FieldAut K σ x) =
      fieldExtension K σ * coordinatePSLAction K x * (fieldExtension K σ)⁻¹ := by
  rw [← coordinatePGLAction_toPGL, psl2FieldAut_toPGL, ← coordinateSemilinearAction_inl,
    ← coordinatePGLAction_toPGL, ← coordinateSemilinearAction_inl]
  have h := SemidirectProduct.inl_aut (φ := pgl2FieldAut K) σ
    (Matrix.ProjectiveSpecialLinearGroup.toPGL x)
  rw [h]
  simp only [map_mul, map_inv, coordinateSemilinearAction_inr, coordinateSemilinearAction_inl]

theorem coordinatePSLAction_semilinearAction (e : PGammaL2 K) (x : PSL2 K) :
    coordinatePSLAction K (semilinearAction K e x) =
      coordinateSemilinearAction K e * coordinatePSLAction K x *
        (coordinateSemilinearAction K e)⁻¹ := by
  have hl : ∀ (A : PGL2 K) (y : PSL2 K),
      coordinatePSLAction K (semilinearAction K (SemidirectProduct.inl A) y) =
      coordinateSemilinearAction K (SemidirectProduct.inl A) * coordinatePSLAction K y *
        (coordinateSemilinearAction K (SemidirectProduct.inl A))⁻¹ := by
    intro A y
    rw [semilinearAction_inl, ← coordinatePGLAction_toPGL, toPGL_pglAction, map_mul, map_mul,
      coordinatePGLAction_toPGL, coordinateSemilinearAction_inl, map_inv]
  have hr : ∀ (τ : K ≃+* K) (y : PSL2 K),
      coordinatePSLAction K (semilinearAction K (SemidirectProduct.inr τ) y) =
      coordinateSemilinearAction K (SemidirectProduct.inr τ) * coordinatePSLAction K y *
        (coordinateSemilinearAction K (SemidirectProduct.inr τ))⁻¹ := by
    intro τ y
    rw [semilinearAction_inr, coordinateSemilinearAction_inr]
    exact coordinatePSLAction_psl2FieldAut K τ y
  have hmul : ∀ e₁ e₂ : PGammaL2 K,
      (∀ y, coordinatePSLAction K (semilinearAction K e₁ y) =
        coordinateSemilinearAction K e₁ * coordinatePSLAction K y *
          (coordinateSemilinearAction K e₁)⁻¹) →
      (∀ y, coordinatePSLAction K (semilinearAction K e₂ y) =
        coordinateSemilinearAction K e₂ * coordinatePSLAction K y *
          (coordinateSemilinearAction K e₂)⁻¹) →
      ∀ y, coordinatePSLAction K (semilinearAction K (e₁ * e₂) y) =
        coordinateSemilinearAction K (e₁ * e₂) * coordinatePSLAction K y *
          (coordinateSemilinearAction K (e₁ * e₂))⁻¹ := by
    intro e₁ e₂ h₁ h₂ y
    simp only [map_mul, MulAut.mul_apply, h₁, h₂, mul_inv_rev]
    group
  rw [← SemidirectProduct.inl_left_mul_inr_right e]
  exact hmul _ _ (hl _) (hr _) x

end Compat

section Fixed

variable {K : Type} [Field K] [Finite K]

theorem psl2FieldAut_apply_eq_iff (σ : K ≃+* K) (x : PSL2 K) :
    psl2FieldAut K σ x = x ↔
      coordinatePSLAction K x ∈ Subgroup.centralizer {fieldExtension K σ} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := coordinatePSLAction_psl2FieldAut K σ x
  constructor
  · intro hx
    rw [hx] at h
    calc coordinatePSLAction K x * fieldExtension K σ
        = (fieldExtension K σ * coordinatePSLAction K x * (fieldExtension K σ)⁻¹) *
            fieldExtension K σ := by rw [← h]
      _ = fieldExtension K σ * coordinatePSLAction K x := by group
  · intro hc
    apply coordinatePSLAction_injective K
    rw [h, ← hc]
    group

noncomputable abbrev subfieldG (σ : K ≃+* K) : Subgroup (Equiv.Perm (Omega K)) :=
  ((coordinateG (fixedSubfield K σ)).subgroupOf
    (coordinateD (fixedSubfield K σ))).map
    ((coordinateD K).subtype.comp
      (CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer.subfieldD
        (fixedSubfield K σ)))

theorem map_fixed_psl2FieldAut_eq {p : ℕ} (hodd : Odd p) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    (signalizerFixedSubgroup (psl2FieldAut K σ)).map (coordinatePSLAction K) = subfieldG σ := by
  obtain ⟨-, -, -, hG, -, -⟩ :=
    CFSG.RankThree.LinearTwo.linear_two_odd_field_fixed_group_and_centralizer K σ hodd hσ
  rw [subfieldG, ← hG]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, (psl2FieldAut_apply_eq_iff σ x).mp hx⟩
    rw [← coordinatePSLAction_range_eq_G]
    exact ⟨x, rfl⟩
  · rintro ⟨hyG, hyc⟩
    rw [← coordinatePSLAction_range_eq_G] at hyG
    obtain ⟨x, rfl⟩ := hyG
    exact ⟨x, (psl2FieldAut_apply_eq_iff σ x).mpr hyc, rfl⟩

theorem nonempty_mulEquiv_fixed_psl2FieldAut {p : ℕ} (hodd : Odd p) {σ : K ≃+* K}
    (hσ : orderOf σ = p) :
    Nonempty (signalizerFixedSubgroup (psl2FieldAut K σ) ≃*
      PSL2 (fixedSubfield K σ)) := by
  obtain ⟨-, hinj, -⟩ :=
    CFSG.RankThree.LinearTwo.linear_two_odd_field_fixed_group_and_centralizer K σ hodd hσ
  set k := fixedSubfield K σ with hk
  set j := (coordinateD K).subtype.comp
    (CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer.subfieldD k) with hj
  have hjinj : Function.Injective j := fun a b h => hinj (Subtype.ext h)
  have hC := map_fixed_psl2FieldAut_eq hodd hσ
  have hle : coordinateG k ≤ coordinateD k := coordinateG_le_D k
  exact ⟨((Subgroup.equivMapOfInjective _ (coordinatePSLAction K)
      (coordinatePSLAction_injective K)).trans
    ((MulEquiv.subgroupCongr hC).trans
      ((Subgroup.equivMapOfInjective _ j hjinj).symm.trans
        ((Subgroup.subgroupOfEquivOfLe hle).trans (pslEquivCoordinateG k).symm))))⟩

theorem mem_zpowers_of_fixes_psl2 {p : ℕ} (hodd : Odd p) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (g : MulAut (PSL2 K)) (hg : ∀ x ∈ signalizerFixedSubgroup (psl2FieldAut K σ), g x = x) :
    g ∈ Subgroup.zpowers (psl2FieldAut K σ) := by
  obtain ⟨-, -, -, -, hcent, -⟩ :=
    CFSG.RankThree.LinearTwo.linear_two_odd_field_fixed_group_and_centralizer K σ hodd hσ
  have hC := map_fixed_psl2FieldAut_eq hodd hσ
  set e := (semilinearEquivAut K).symm g with he
  have hge : semilinearAction K e = g := (semilinearEquivAut K).apply_symm_apply g
  have hmemE : coordinateSemilinearAction K e ∈ coordinateE K := by
    rw [← coordinateSemilinearAction_range_eq_E]
    exact ⟨e, rfl⟩
  have hmemc : coordinateSemilinearAction K e ∈ Subgroup.centralizer
      ((subfieldG σ : Subgroup (Equiv.Perm (Omega K))) : Set (Equiv.Perm (Omega K))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy
    rw [← hC] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 := coordinatePSLAction_semilinearAction K e x
    rw [hge, hg x hx] at h1
    calc coordinatePSLAction K x * coordinateSemilinearAction K e
        = (coordinateSemilinearAction K e * coordinatePSLAction K x *
            (coordinateSemilinearAction K e)⁻¹) * coordinateSemilinearAction K e := by rw [← h1]
      _ = coordinateSemilinearAction K e * coordinatePSLAction K x := by group
  have hmem : coordinateSemilinearAction K e ∈ Subgroup.zpowers (fieldExtension K σ) := by
    rw [← hcent]
    exact ⟨hmemc, hmemE⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hi' : coordinateSemilinearAction K (SemidirectProduct.inr σ ^ i) =
      coordinateSemilinearAction K e := by
    rw [map_zpow, coordinateSemilinearAction_inr]
    exact hi
  have hei : e = SemidirectProduct.inr σ ^ i := (coordinateSemilinearAction_injective K hi').symm
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  rw [← hge, hei, map_zpow, semilinearAction_inr]

theorem exists_fieldAut_orderOf_psl2 {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpT : ¬ p ∣ Nat.card (PSL2 K)) {f : MulAut (PSL2 K)} (hf : orderOf f = p) :
    ∃ σ : K ≃+* K, orderOf σ = p := by
  have : Fact p.Prime := ⟨hp⟩
  set e := (semilinearEquivAut K).symm f with he
  have hep : orderOf e = p := by rw [he, MulEquiv.orderOf_eq]; exact hf
  have hep1 : e ^ p = 1 := by rw [← hep]; exact pow_orderOf_eq_one e
  have hσp : e.right ^ p = 1 := by
    have h := congrArg SemidirectProduct.rightHom hep1
    rwa [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at h
  refine ⟨e.right, orderOf_eq_prime hσp ?_⟩
  intro hσ1
  have heA : e = SemidirectProduct.inl e.left := by
    rw [← SemidirectProduct.inl_left_mul_inr_right e, hσ1]
    simp
  set A := e.left with hA
  have hAp : A ^ p = 1 := by
    have h : (SemidirectProduct.inl A : PGammaL2 K) ^ p = 1 := by rw [← heA]; exact hep1
    rw [← map_pow] at h
    exact SemidirectProduct.inl_injective (by simpa using h)
  obtain ⟨m, hm⟩ := hodd
  have hsq : A * A ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
    (CFSG.ABGDGroups.mul_mem_range_toPGL_iff A A).mpr Iff.rfl
  have hmem : A ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    have h1 : A ^ p = (A * A) ^ m * A := by rw [hm, pow_succ, pow_mul, sq]
    have h2 : (A * A) ^ m * A ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
      rw [← h1, hAp]
      exact one_mem _
    exact ((CFSG.ABGDGroups.mul_mem_range_toPGL_iff _ A).mp h2).mp (pow_mem hsq m)
  obtain ⟨x, hx⟩ := hmem
  have hxp : x ^ p = 1 := by
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [map_pow, hx, hAp, map_one]
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one] at hx
    have : e = 1 := by rw [heA, ← hx]; simp
    rw [this, orderOf_one] at hep
    exact hp.one_lt.ne' hep.symm
  exact hpT ((orderOf_eq_prime hxp hx1) ▸ orderOf_dvd_natCard x)

end Fixed

theorem fieldClauses_psl2
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpT : ¬ p ∣ Nat.card (PSL2 K))
    (hbig : ∀ σ : K ≃+* K, orderOf σ = p →
      4 ≤ Nat.card (fixedSubfield K σ)) :
    FieldClauses p (PSL2 K) := by
  rintro ⟨f, hf⟩
  obtain ⟨σ, hσ⟩ := exists_fieldAut_orderOf_psl2 hp hodd hpT hf
  have hord : orderOf (psl2FieldAut K σ) = p := by
    rw [orderOf_injective (psl2FieldAut K) (psl2FieldAut_injective K) σ]
    exact hσ
  obtain ⟨e⟩ := nonempty_mulEquiv_fixed_psl2FieldAut hodd hσ
  obtain ⟨hsimple, hns⟩ := psl2_simple_not_isSolvable (hbig σ hσ)
  have hsC : IsSimpleGroup (signalizerFixedSubgroup (psl2FieldAut K σ)) := e.isSimpleGroup
  have hnsC : ¬ Group.IsSolvable (signalizerFixedSubgroup (psl2FieldAut K σ)) := fun h =>
    hns (isSolvable_of_mulEquiv' e.symm)
  have hnC : ∃ a b : signalizerFixedSubgroup (psl2FieldAut K σ), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hnsC (Group.isSolvable_of_comm fun a b => hcon a b)
  have hF := fStarSimple_of_simple hsC hnC
  have hNL : NonLocalized (signalizerFixedSubgroup (psl2FieldAut K σ)) :=
    nonLocalized_of_not_isSolvable_psl2 _ hnsC
  exact ⟨psl2FieldAut K σ, hord, fixedClauses_of_stabilizer hord hF (fun _ => hNL)
    (mem_zpowers_of_fixes_psl2 hodd hσ)⟩

theorem nearOrField_statedPSL2
    {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSL 2 ℓ f) (hp : p.Prime)
    (hodd : Odd p) (hpT : ¬ p ∣ Nat.card T) :
    signalizerNearPSolvable p T ∨ FieldClauses p T := by
  obtain ⟨⟨hℓ, hf, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have eP := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 ℓ f (by omega) hK
  let e : T ≃* PSL2 (GaloisField ℓ f) := eT.trans eP
  have hpT' : ¬ p ∣ Nat.card (PSL2 (GaloisField ℓ f)) := by
    rwa [← Nat.card_congr e.toEquiv]
  by_cases hnear : (ℓ = 2 ∨ ℓ = 3) ∧ f = p
  · obtain ⟨hℓ23, rfl⟩ := hnear
    refine Or.inl (CFSG.SignalizerFunctorTheorem.TransportA.nearPSolvable_of_mulEquiv e.symm ?_)
    rcases hℓ23 with rfl | rfl
    · exact nearPSolvable_psl2_even hp hodd ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpT')
    · exact nearPSolvable_psl2_three hp hodd ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpT')
  · refine Or.inr (FieldClauses.of_mulEquiv e.symm (fieldClauses_psl2 hp hodd hpT' ?_))
    intro σ hσ
    have hcardK : Nat.card (GaloisField ℓ f) = ℓ ^ f := GaloisField.card ℓ f (by omega)
    obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.LinearTwo.card_fixedSubfield hℓ (by omega) hcardK σ
    rw [hσ] at hdvd hcard
    by_contra hlt
    have h2 : 2 ≤ Nat.card (fixedSubfield
        (GaloisField ℓ f) σ) := Finite.one_lt_card
    apply hnear
    obtain ⟨c, hc⟩ := hdvd
    have hfc : f / p = c := by
      rw [hc, Nat.mul_div_cancel_left c hp.pos]
    rw [hfc] at hcard
    have h23 : ℓ ^ c = 2 ∨ ℓ ^ c = 3 := by omega
    rcases h23 with h | h
    · obtain ⟨rfl, hc1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp h
      exact ⟨Or.inl rfl, by rw [hc, hc1, mul_one]⟩
    · obtain ⟨rfl, hc1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h
      exact ⟨Or.inr rfl, by rw [hc, hc1, mul_one]⟩

end CFSG.SignalizerFunctorTheorem.CatalogBridge
