module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGLayer

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.StandardType.D4Rank CFSG.Assembly.LowTwoRank

namespace L613KG

variable {K : Type} [Field K]

@[expose] noncomputable def zStd [Finite K] [CharP K 2] (ω : Kˣ) : Om8 K :=
  dg (fun k => if k = 3 then 1 else ω)

variable [Finite K] [CharP K 2]

theorem zStd_pow_three {ω : Kˣ} (hω3 : ω ^ 3 = 1) : zStd ω ^ 3 = 1 := by
  rw [zStd, ← dgHom_apply, ← map_pow]
  have h : (fun k : Fin 4 => if k = 3 then (1 : Kˣ) else ω) ^ 3 = 1 := by
    funext k
    by_cases hk : k = 3 <;> simp [hk, hω3]
  rw [h, map_one]

theorem omFixDim_zStd {ω : Kˣ} (hω : orderOf ω = 3) : omFixDim (zStd ω) = 2 := by
  classical
  obtain ⟨h1, -, -⟩ := units_facts hω
  have hω1 : (ω : K) ≠ 1 := fun h => h1 (Units.ext h)
  rw [zStd, omFixDim_eq_card_of_diag (act_dg _), Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, ← Equiv.sum_comp (plusIndexEquiv 4), Fintype.sum_sum_type,
    Fin.sum_univ_four, Fin.sum_univ_four]
  change (if ((twHom (fun k => if k = 3 then 1 else ω) (ie 0) : Kˣ) : K) = 1 then 1 else 0) +
      (if ((twHom (fun k => if k = 3 then 1 else ω) (ie 1) : Kˣ) : K) = 1 then 1 else 0) +
      (if ((twHom (fun k => if k = 3 then 1 else ω) (ie 2) : Kˣ) : K) = 1 then 1 else 0) +
      (if ((twHom (fun k => if k = 3 then 1 else ω) (ie 3) : Kˣ) : K) = 1 then 1 else 0) +
      ((if ((twHom (fun k => if k = 3 then 1 else ω) (jf 0) : Kˣ) : K) = 1 then 1 else 0) +
      (if ((twHom (fun k => if k = 3 then 1 else ω) (jf 1) : Kˣ) : K) = 1 then 1 else 0) +
      (if ((twHom (fun k => if k = 3 then 1 else ω) (jf 2) : Kˣ) : K) = 1 then 1 else 0) +
      (if ((twHom (fun k => if k = 3 then 1 else ω) (jf 3) : Kˣ) : K) = 1 then 1 else 0)) = 2
  simp only [twHom_ie, twHom_jf]
  simp [hω1]

omit [Finite K] in
theorem omFixDim_two_four_of_tau {τ : MulAut (Om8 K)}
    (h6 : ∀ x : Om8 K, x ^ 3 = 1 → omFixDim x = 6 →
      omFixDim (τ x) = 0 ∧ omFixDim (τ⁻¹ x) = 0)
    (h0 : ∀ x : Om8 K, x ^ 3 = 1 → omFixDim x = 0 →
      omFixDim (τ x) = 6 ∨ omFixDim (τ⁻¹ x) = 6)
    (hsq : τ * τ = τ⁻¹) {y : Om8 K} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (h : omFixDim y = 2 ∨ omFixDim y = 4) : omFixDim (τ y) = 2 ∨ omFixDim (τ y) = 4 := by
  have hy3' : (τ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hy1' : τ y ≠ 1 := fun h' => hy1 (by rw [← map_one τ] at h'; exact τ.injective h')
  have hle : omFixDim (τ y) ≤ 8 := by
    have := Submodule.finrank_le (LinearMap.ker (omRep (τ y) - 1))
    rwa [Module.finrank_fin_fun] at this
  have h8 : omFixDim (τ y) ≠ 8 := fun h' => hy1' (eq_one_of_omFixDim h')
  obtain ⟨j, hj⟩ := omFixDim_even (τ y) hy3'
  have hinv : τ⁻¹ (τ y) = y := MulAut.inv_apply_self _ τ y
  have hn6 : omFixDim (τ y) ≠ 6 := by
    intro h6'
    have := (h6 _ hy3' h6').2
    rw [hinv] at this
    omega
  have hn0 : omFixDim (τ y) ≠ 0 := by
    intro h0'
    rcases h0 _ hy3' h0' with h' | h'
    ·
      have e : τ (τ y) = τ⁻¹ y := by rw [← MulAut.mul_apply, hsq]
      rw [e] at h'
      have hz3 : (τ⁻¹ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
      have := (h6 _ hz3 h').1
      rw [MulAut.apply_inv_self] at this
      omega
    · rw [hinv] at h'
      omega
  omega

theorem omFixDim_two_four_aut (β : MulAut (Om8 K)) {x : Om8 K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (h : omFixDim x = 2 ∨ omFixDim x = 4) : omFixDim (β x) = 2 ∨ omFixDim (β x) = 4 := by
  have hcls := ggD4TrialityClassInput_holds K
  obtain ⟨ι, ⟨γ, rfl⟩, k, c, hc, hβ⟩ := exists_inner_mul_theta_pow_mul β
  have hcx : omFixDim (c x) = omFixDim x := by
    obtain ⟨σ, rfl | rfl⟩ := hc
    · exact omFixDim_fieldAutP σ x
    · rw [MulAut.mul_apply, omFixDim_plusRefl, omFixDim_fieldAutP]
  have hcx3 : (c x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hcx1 : c x ≠ 1 := fun h' => hx1 (by rw [← map_one c] at h'; exact c.injective h')
  have hθ : ∀ y : Om8 K, y ^ 3 = 1 → y ≠ 1 → (omFixDim y = 2 ∨ omFixDim y = 4) →
      (omFixDim (theta y) = 2 ∨ omFixDim (theta y) = 4) ∧
        (omFixDim (theta⁻¹ y) = 2 ∨ omFixDim (theta⁻¹ y) = 4) := by
    intro y hy3 hy1 hy
    refine ⟨omFixDim_two_four_of_tau (fun x hx3 hx6 => (hcls x hx3).1 hx6)
      (fun x hx3 hx0 => (hcls x hx3).2 hx0) ?_ hy3 hy1 hy,
      omFixDim_two_four_of_tau (τ := theta⁻¹) (fun x hx3 hx6 => ?_) (fun x hx3 hx0 => ?_) ?_
        hy3 hy1 hy⟩
    · rw [← theta_sq, _root_.sq]
    · rw [inv_inv]
      exact ((hcls x hx3).1 hx6).symm
    · rw [inv_inv]
      exact ((hcls x hx3).2 hx0).symm
    · rw [inv_inv, ← mul_inv_rev, ← _root_.sq, theta_sq, inv_inv]
  have hk : (theta : MulAut (Om8 K)) ^ k = theta ^ (k % 3) := pow_eq_pow_mod k theta_cube
  have hk3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hth : omFixDim ((theta ^ k) (c x)) = 2 ∨ omFixDim ((theta ^ k) (c x)) = 4 := by
    rw [hk]
    interval_cases (k % 3)
    · rw [pow_zero, MulAut.one_apply, hcx]
      exact h
    · rw [pow_one]
      exact (hθ _ hcx3 hcx1 (hcx ▸ h)).1
    · rw [theta_sq]
      exact (hθ _ hcx3 hcx1 (hcx ▸ h)).2
  rw [hβ, MulAut.mul_apply, MulAut.mul_apply, omFixDim_conj]
  exact hth

end L613KG

section Inputs

open L613KG

@[expose] def GGD4ClassThreeConjInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ z z' : Om8 K, z ^ 3 = 1 → z' ^ 3 = 1 → omFixDim z = 2 → omFixDim z' = 2 →
      ∃ g : Om8 K, z' = g * z * g⁻¹

@[expose] def GGD4ClassThreeStdSylowInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ ω : Kˣ, orderOf ω = 3 → ¬ 3 ∣ (Subgroup.centralizer {zStd ω}).index

@[expose] def GGD4ClassThreeLayerStdInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ ω : Kˣ, orderOf ω = 3 →
      ∃ S : Subgroup (Om8 K), ⁅S, S⁆ = S ∧ zStd ω ∈ S ∧ S ≤ Subgroup.centralizer {zStd ω} ∧
        (∀ X : Subgroup (Om8 K), X ≤ Subgroup.centralizer {zStd ω} → ⁅X, X⁆ = X → X ≤ S) ∧
        Nat.card S ≤ 3 * Nat.card (StatedProj (StatedSL 3 K))

end Inputs

namespace L613KG

variable {K : Type} [Field K]

theorem centralizer_conj_eq {G : Type} [Group G] (g x : G) :
    Subgroup.centralizer {g * x * g⁻¹} =
      (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [SetLike.mem_coe]
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
      _ = x * (g⁻¹ * y * g) := by group
  · rintro ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * s * g⁻¹ * (g * x * g⁻¹) = g * (s * x) * g⁻¹ := by group
      _ = g * (x * s) * g⁻¹ := by rw [hs]
      _ = g * x * g⁻¹ * (g * s * g⁻¹) := by group

theorem centralizer_mulAut_eq {G : Type} [Group G] (β : MulAut G) (x : G) :
    Subgroup.centralizer {β x} = (Subgroup.centralizer {x}).map β.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨β.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe]
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    have h := congrArg β.symm hy
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
    exact h
  · rintro ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, hs, map_mul]

theorem index_map_mulAut {G : Type} [Group G] (β : MulAut G) (H : Subgroup G) :
    (H.map β.toMonoidHom).index = H.index :=
  Subgroup.index_map_eq (f := β.toMonoidHom) H β.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr β.injective]; exact bot_le)

end L613KG

section Reductions

open L613KG

theorem ggD4ClassThreeLayerInput_of_std (hconj : GGD4ClassThreeConjInput)
    (hstd : GGD4ClassThreeLayerStdInput) : GGD4ClassThreeLayerInput := by
  intro K _ _ _ hK3 z hz3 hz2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact hK3)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  obtain ⟨S, hSp, hzS, hSC, hSmax, hScard⟩ := hstd K hK3 ω hω
  obtain ⟨g, rfl⟩ := hconj K hK3 (zStd ω) z (zStd_pow_three hω3) hz3 (omFixDim_zStd hω) hz2
  refine ⟨S.map (MulAut.conj g).toMonoidHom, ?_, ⟨zStd ω, hzS, rfl⟩, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hSp]
  · rw [centralizer_conj_eq]
    exact Subgroup.map_mono hSC
  · intro X hX hXp
    have h1 : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer {zStd ω} := by
      have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX
      rwa [centralizer_conj_eq, Subgroup.map_map,
        show ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
          MonoidHom.id (Om8 K) from MonoidHom.ext fun y => by
            simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
              MonoidHom.id_apply]
            group,
        Subgroup.map_id] at h
    have h2 := hSmax _ h1 (by rw [← Subgroup.map_commutator, hXp])
    intro x hx
    refine ⟨g⁻¹ * x * g, h2 ⟨x, hx, ?_⟩, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hScard

theorem ggD4ClassThreeCentralInput_of_std (hconj : GGD4ClassThreeConjInput)
    (hsyl : GGD4ClassThreeStdSylowInput) : GGD4ClassThreeCentralInput := by
  intro K _ _ _ hK3 z hz3 hz2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact hK3)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  obtain ⟨g, hg⟩ := hconj K hK3 (zStd ω) z (zStd_pow_three hω3) hz3 (omFixDim_zStd hω) hz2
  have hidx : ¬ 3 ∣ (Subgroup.centralizer {z}).index := by
    rw [hg, centralizer_conj_eq, index_map_mulAut]
    exact hsyl K hK3 ω hω
  refine ⟨hidx, fun β => ?_⟩
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [omFixDim_one] at hz2
    exact absurd hz2 (by norm_num)
  have hβ3 : (β z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hβidx : ¬ 3 ∣ (Subgroup.centralizer {β z}).index := by
    rw [centralizer_mulAut_eq, index_map_mulAut]
    exact hidx
  have hβ2 : omFixDim (β z) = 2 :=
    (omFixDim_two_four_aut β hz3 hz1 (Or.inl hz2)).resolve_right
      (omFixDim_ne_four_of_not_dvd hK3 hβidx)
  exact hconj K hK3 z (β z) hz3 hβ3 hz2 hβ2

end Reductions

section Assembly

theorem ggD4TrialityCentralInput_of_std (hconj : GGD4ClassThreeConjInput)
    (hstd : GGD4ClassThreeLayerStdInput) : GGD4TrialityCentralInput :=
  ggD4TrialityCentralInput_of_classThree (ggD4ClassThreeLayerInput_of_std hconj hstd)

theorem ggSixTrialityDCentralInput_of_std (h6 : GGSixTrialityDClassThreeInput)
    (hconj : GGD4ClassThreeConjInput) (hsyl : GGD4ClassThreeStdSylowInput) :
    GGSixTrialityDCentralInput :=
  ggSixTrialityDCentralInput_of_om8 h6 (ggD4ClassThreeCentralInput_of_std hconj hsyl)

theorem ggSixTrialityInput_of_std (h611 : GGSixLSixElevenInput)
    (hconj : GGD4ClassThreeConjInput) (hsyl : GGD4ClassThreeStdSylowInput)
    (hstd : GGD4ClassThreeLayerStdInput) (h6 : GGSixTrialityDClassThreeInput) :
    GGSixTrialityInput :=
  ggSixTrialityInput_of_lSixEleven_central h611 (ggD4TrialityCentralInput_of_std hconj hstd)
    (ggSixTrialityDCentralInput_of_std h6 hconj hsyl)

end Assembly

end CFSG.StandardType
