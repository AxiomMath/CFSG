module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGOuter
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.StandardType.D4Rank QuadraticMap
open scoped Matrix

namespace L613KG

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section FieldAut

omit [Finite K] [CharP K 2] in
theorem act_fieldAutP (σ : K ≃+* K) (x : Om8 K) (v : Fin (2 * 4) → K) :
    act (AutOm.fieldAutP 4 σ x) (coordinateFieldMap (2 * 4) σ v) =
      coordinateFieldMap (2 * 4) σ (act x v) := by
  have h := coordinateFieldMap_matrix σ (x : GL (Fin (2 * 4)) K) v
  rw [matrixLinearEquiv_apply, matrixLinearEquiv_apply] at h
  rw [act, act, h, fieldAutP_val]

omit [Finite K] in
theorem act_X8_rootC (c : K) :
    act (X8 rootC c) (AutOm.pvec 3 false) = AutOm.pvec 3 false + c • AutOm.pvec 0 false := by
  rw [act, X8_mulVec (by decide) toStdD_rootC c, AutOm.eichlerC, AutOm.polar_pvec,
    polar_smul_right, AutOm.polar_pvec, QuadraticMap.map_smul, AutOm.form_pvec]
  simp

omit [Finite K] in
theorem eq_one_of_fieldAutP_eq_one {τ : K ≃+* K} (h : AutOm.fieldAutP 4 τ = 1) : τ = 1 := by
  refine RingEquiv.ext fun c => ?_
  have h1 := fieldAutP_X8 τ rootC_mem c
  rw [h, MulAut.one_apply] at h1
  have h2 := congrArg (fun x => act x (AutOm.pvec 3 false)) h1
  simp only [act_X8_rootC] at h2
  have h3 := congrFun (add_left_cancel h2) (jf 0)
  rw [AutOm.pvec_false] at h3
  simpa using h3.symm

theorem exists_field_form {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1) (hin : α ∉ inner (Om8 K))
    (hsl : ∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = α) :
    ∃ (γ : Om8 K) (σ : K ≃+* K), orderOf σ = 3 ∧ α = MulAut.conj γ * AutOm.fieldAutP 4 σ := by
  obtain ⟨g, rfl⟩ := hsl
  obtain ⟨ι, hι, c, hc, hgc⟩ := exists_inner_mul_plusCompl_of_pair g
  obtain ⟨γ, rfl⟩ := hι
  rw [hgc] at hα3 hin ⊢
  obtain ⟨σ, rfl | rfl⟩ := hc
  · obtain ⟨γ', hγ'⟩ := conj_mul_cube (AutOm.fieldAutP 4 σ) γ
    rw [hα3] at hγ'
    have hmem : AutOm.fieldAutP 4 (σ ^ 3) ∈ inner (Om8 K) := by
      have e : AutOm.fieldAutP 4 (σ ^ 3) = MulAut.conj γ'⁻¹ := by
        rw [map_pow, map_inv]
        exact eq_inv_of_mul_eq_one_right hγ'.symm
      rw [e]
      exact ⟨γ'⁻¹, rfl⟩
    have h1 := (theta_pow_mul_mem_inner 0 ⟨σ ^ 3, Or.inl rfl⟩
      (by rw [pow_zero, one_mul]; exact hmem)).2
    have hσ3 : σ ^ 3 = 1 := eq_one_of_fieldAutP_eq_one h1
    have hσ1 : σ ≠ 1 := fun h => hin (by rw [h, map_one, mul_one]; exact ⟨γ, rfl⟩)
    exact ⟨γ, σ, orderOf_eq_prime hσ3 hσ1, rfl⟩
  · exfalso
    set r : MulAut (Om8 K) := AutOm.plusRefl one_le_four with hr
    set φ : MulAut (Om8 K) := AutOm.fieldAutP 4 σ with hφ
    have hrr : r * r = 1 := AutOm.plusRefl_mul_self one_le_four
    have hrφ : Commute r φ := AutOm.plusRefl_mul_fieldAutP one_le_four σ
    have hcube : (r * φ) ^ 3 = r * AutOm.fieldAutP 4 (σ ^ 3) := by
      rw [hrφ.mul_pow, map_pow, pow_succ, pow_succ, pow_one, hrr, one_mul]
    obtain ⟨γ', hγ'⟩ := conj_mul_cube (r * φ) γ
    rw [hα3, hcube] at hγ'
    have hmem : r * AutOm.fieldAutP 4 (σ ^ 3) ∈ inner (Om8 K) := by
      rw [eq_inv_of_mul_eq_one_right hγ'.symm, ← map_inv]
      exact ⟨γ'⁻¹, rfl⟩
    have h1 := (theta_pow_mul_mem_inner 0 ⟨σ ^ 3, Or.inr rfl⟩
      (by rw [pow_zero, one_mul]; exact hmem)).2
    have hr' : r = (AutOm.fieldAutP 4 (σ ^ 3))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hrθ : r * theta = theta * r := by
      rw [hr']
      exact ((Commute.inv_right (theta_fieldAutP (σ ^ 3) : Commute theta _)).eq).symm
    have hθ : (theta : MulAut (Om8 K)) = theta⁻¹ := by
      calc (theta : MulAut (Om8 K)) = r * theta * r := by
            rw [hrθ, mul_assoc, hrr, mul_one]
        _ = theta⁻¹ := plusRefl_theta_plusRefl
    have h2 : (theta : MulAut (Om8 K)) ^ 2 = 1 := by
      rw [_root_.sq]
      nth_rw 2 [hθ]
      exact mul_inv_cancel _
    rw [theta_sq] at h2
    exact theta_pow_ne_one (K := K) (k := 1) (Or.inl rfl) (by rw [pow_one]; exact inv_eq_one.mp h2)

end FieldAut

section Sylow

omit [Field K] [Finite K] [CharP K 2] in
theorem pow_succ_dvd_cube_sub_one {r v : ℕ} (hr : 1 ≤ r) (hv : 1 ≤ v) (h : 3 ^ v ∣ r - 1) :
    3 ^ (v + 1) ∣ r ^ 3 - 1 := by
  obtain ⟨m, hm⟩ := h
  have hr' : r = 3 ^ v * m + 1 := by omega
  have hx3 : 3 ∣ 3 ^ v * m := dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) m
  have e : r ^ 3 - 1 = 3 ^ v * m * ((3 ^ v * m) ^ 2 + 3 * (3 ^ v * m) + 3) := by
    rw [hr']
    apply Nat.sub_eq_of_eq_add
    ring
  rw [e, pow_succ]
  refine mul_dvd_mul (dvd_mul_right _ _) ?_
  obtain ⟨y, hy⟩ := hx3
  exact ⟨3 * y ^ 2 + 3 * y + 1, by rw [hy]; ring⟩

omit [Finite K] [CharP K 2] in
theorem act_eq_zero_iff (x : Om8 K) (y : Fin (2 * 4) → K) : act x y = 0 ↔ y = 0 := by
  constructor
  · intro h
    rw [← act_inv_act x y, h]
    exact Matrix.mulVec_zero _
  · rintro rfl
    exact Matrix.mulVec_zero _

theorem _root_.CFSG.StandardType.ggD4FieldSylowInput_holds : GGD4FieldSylowInput := by
  intro K _ _ _ hK3 α hα3 hsl S hS
  by_contra hin
  obtain ⟨γ, σ, hσ, rfl⟩ := exists_field_form hα3 hin hsl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Nat.card Kˣ with hN
  have hN0 : N ≠ 0 := Nat.card_pos.ne'
  have h3N : 3 ∣ N := by rw [hN, Nat.card_units]; exact hK3
  obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hogen : orderOf gen = N := orderOf_eq_card_of_forall_mem_zpowers hgen
  set v := N.factorization 3 with hv
  have hv1 : 1 ≤ v := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hN0).mp h3N
  obtain ⟨b, hb⟩ := Nat.ordProj_dvd N 3
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact hN0 hb
  set lam := gen ^ b with hlam
  have hlamo : orderOf lam = 3 ^ v := by
    rw [hlam, orderOf_pow_of_dvd hb0 (by rw [hogen]; exact Dvd.intro_left _ hb.symm), hogen]
    nth_rw 1 [hb]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)
  have h3v : 3 ≤ 3 ^ v := by
    calc 3 = 3 ^ 1 := rfl
      _ ≤ 3 ^ v := Nat.pow_le_pow_right (by norm_num) hv1
  have hlam1 : (lam : K) ≠ 1 := by
    intro h
    have h' : lam = 1 := Units.ext h
    rw [h', orderOf_one] at hlamo
    omega
  set t : Om8 K := dg (Pi.mulSingle (0 : Fin 4) lam) with ht
  have ht3 : t ^ (3 ^ v) = 1 := by
    rw [ht, ← dgHom_apply, ← map_pow, ← Pi.mulSingle_pow, ← hlamo, pow_orderOf_eq_one,
      Pi.mulSingle_one, map_one]
  have htp : IsPGroup 3 (Subgroup.zpowers t) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨v, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (t ^ k) ^ (3 ^ v) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, ht3, one_zpow]
  obtain ⟨S'', hS''⟩ := htp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Om8 K) S S''
  have htS : t ∈ (S'' : Subgroup (Om8 K)) := hS'' (Subgroup.mem_zpowers t)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htS
  obtain ⟨s, hs, hst⟩ := htS
  have hst' : g * s * g⁻¹ = t := by
    rw [MulAut.smul_def, MulAut.conj_apply] at hst
    exact hst
  have hfix := hS s hs
  rw [MulAut.mul_apply, MulAut.conj_apply] at hfix
  have hφs : AutOm.fieldAutP 4 σ s = γ⁻¹ * s * γ := by
    calc AutOm.fieldAutP 4 σ s = γ⁻¹ * (γ * AutOm.fieldAutP 4 σ s * γ⁻¹) * γ := by group
      _ = γ⁻¹ * s * γ := by rw [hfix]
  have hte0 : act t (Pi.single (ie 0) 1) = (lam : K) • Pi.single (ie 0) 1 := by
    rw [ht, act_dg_single, twHom_ie, Pi.mulSingle_eq_same]
  have hsv0 : act s (act g⁻¹ (Pi.single (ie 0) 1)) = (lam : K) • act g⁻¹ (Pi.single (ie 0) 1) := by
    have e : s = g⁻¹ * t * g := by rw [← hst']; group
    rw [e, act_mul, act_mul, act_act_inv, hte0, act_smul]
  set w := coordinateFieldMap (2 * 4) σ (act g⁻¹ (Pi.single (ie 0) 1)) with hw
  have hw' : act (γ⁻¹ * s * γ) w = σ (lam : K) • w := by
    rw [← hφs, hw, act_fieldAutP, hsv0, coordinateFieldMap_smul]
  set u := act g (act γ w) with hu
  have hut : act t u = σ (lam : K) • u := by
    have e1 : act s (act γ w) = σ (lam : K) • act γ w := by
      have e2 : act s (act γ w) = act γ (act (γ⁻¹ * s * γ) w) := by
        rw [act_mul, act_mul, act_act_inv]
      rw [e2, hw', act_smul]
    rw [hu, ← hst', act_mul, act_mul, act_inv_act, e1, act_smul]
  have hu0 : u ≠ 0 := by
    intro h0
    rw [hu, act_eq_zero_iff, act_eq_zero_iff, hw, AddEquiv.map_eq_zero_iff,
      act_eq_zero_iff] at h0
    exact one_ne_zero (congrFun h0 (ie 0) |>.symm.trans (by simp) |>.symm)
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  have hval : ((twHom (Pi.mulSingle (0 : Fin 4) lam) j : Kˣ) : K) = σ (lam : K) := by
    have h1 := congrFun hut j
    rw [ht, act_dg] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    exact mul_right_cancel₀ hj h1
  have hσ1 : σ (lam : K) ≠ 1 := fun h => hlam1 (σ.injective (h.trans σ.map_one.symm))
  have hσlam : σ (lam : K) = lam ∨ σ (lam : K) = (lam : K)⁻¹ := by
    rcases ie_or_jf j with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · rw [twHom_ie] at hval
      by_cases hl : l = 0
      · subst hl
        rw [Pi.mulSingle_eq_same] at hval
        exact Or.inl hval.symm
      · rw [Pi.mulSingle_eq_of_ne hl, Units.val_one] at hval
        exact absurd hval.symm hσ1
    · rw [twHom_jf] at hval
      by_cases hl : l = 0
      · subst hl
        rw [Pi.mulSingle_eq_same, Units.val_inv_eq_inv_val] at hval
        exact Or.inr hval.symm
      · rw [Pi.mulSingle_eq_of_ne hl, inv_one, Units.val_one] at hval
        exact absurd hval.symm hσ1
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hcube : ∀ x : K, σ (σ (σ x)) = x := fun x => by
    have h1 : (σ ^ 3) x = x := by rw [hσ3]; rfl
    rwa [pow_succ, pow_succ, pow_one] at h1
  have hfixlam : σ (lam : K) = lam := by
    rcases hσlam with h | h
    · exact h
    · exfalso
      have h2 : σ (σ (σ (lam : K))) = (lam : K)⁻¹ := by
        rw [h, map_inv₀, h, inv_inv]
        exact h
      rw [hcube] at h2
      have h3 : lam ^ 2 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, _root_.sq]
        nth_rw 2 [h2]
        exact mul_inv_cancel₀ lam.ne_zero
      have h4 := orderOf_dvd_of_pow_eq_one h3
      rw [hlamo] at h4
      have h5 := Nat.le_of_dvd (by norm_num) h4
      omega
  set R := FixedPoints.subfield (Subgroup.zpowers σ) K with hR
  have hσfin : IsOfFinOrder σ := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hσ3⟩
  have hlamR : (lam : K) ∈ R := by
    rintro ⟨τ, hτ⟩
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp (hσfin.mem_powers_iff_mem_zpowers.mpr hτ)
    change (σ ^ n) (lam : K) = lam
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ]
      change (σ ^ n) (σ (lam : K)) = lam
      rw [hfixlam]
      exact ih (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) n)
  have hcardK : Nat.card K = Nat.card R ^ 3 := by
    have h := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf K σ
    rwa [hσ] at h
  have hlamR1 : lam ^ (Nat.card R - 1) = 1 := by
    have hne : (⟨(lam : K), hlamR⟩ : R) ≠ 0 := fun h => lam.ne_zero (congrArg Subtype.val h)
    have h1 := pow_card_eq_one' (G := Rˣ) (x := Units.mk0 _ hne)
    rw [Nat.card_units] at h1
    apply Units.ext
    have h2 := congrArg (fun x : Rˣ => ((x : R) : K)) h1
    simpa using h2
  have hdvd : 3 ^ v ∣ Nat.card R - 1 := hlamo ▸ orderOf_dvd_of_pow_eq_one hlamR1
  have hR1 : 1 ≤ Nat.card R := Nat.card_pos
  have h1 := pow_succ_dvd_cube_sub_one hR1 hv1 hdvd
  rw [← hcardK, ← Nat.card_units] at h1
  exact Nat.pow_succ_factorization_not_dvd hN0 Nat.prime_three h1

end Sylow

end L613KG

theorem ggD4OuterSylowInput_holds : GGD4OuterSylowInput :=
  ggD4OuterSylowInput_of_field ggD4FieldSylowInput_holds

section Main

theorem ggD4TrialityCentralInput_of_layer (h2 : GGD4SemilinearLayerInput)
    (h4 : GGD4ClassThreeLayerInput) : GGD4TrialityCentralInput :=
  ggD4TrialityCentralInput_of_om8 ggD4OuterSylowInput_holds h2 ggD4CentralClassThreeInput_holds h4

theorem ggSixTrialityInput_of_layer (h611 : GGSixLSixElevenInput)
    (h2 : GGD4SemilinearLayerInput) (h4 : GGD4ClassThreeLayerInput)
    (h5 : GGD4ClassThreeCentralInput) (h6 : GGSixTrialityDClassThreeInput) :
    GGSixTrialityInput :=
  ggSixTrialityInput_of_lSixEleven_central h611 (ggD4TrialityCentralInput_of_layer h2 h4)
    (ggSixTrialityDCentralInput_of_om8 h6 h5)

end Main

end CFSG.StandardType
