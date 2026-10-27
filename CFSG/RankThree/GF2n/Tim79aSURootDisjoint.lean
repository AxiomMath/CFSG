module

public import CFSG.Timmesfeld.Transvection.ModelSUTheta
public import CFSG.Timmesfeld.Transvection.ModelSUNormal

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem exists_smul_eq_of_uTrans_one_eq {v w : Fin m → F}
    (h : uTrans σ v 1 = uTrans σ w 1) : ∃ μ : F, v = μ • w := by
  refine exists_eq_smul_of_uNil_eq (σ := σ) (l := 1) ?_
  rw [uTrans, uTrans] at h
  have h' := add_left_cancel h
  rw [one_smul, one_smul] at h'
  rw [one_smul]
  exact h'

theorem mulVec_eq_self_of_mem_center_of_uForm_ne_zero [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a v : Fin m → F} (hvv : uForm σ v v = 0) (hav : uForm σ a v ≠ 0) {z : SU σ m}
    (hz : z ∈ Subgroup.center (SU σ m)) (hza : suMat σ m z *ᵥ a = a) :
    suMat σ m z *ᵥ v = v := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans hσ hvv h1
  have hzt : z * t * z⁻¹ = t := by
    rw [← Subgroup.mem_center_iff.1 hz t, mul_inv_cancel_right]
  have h2 := suMat_conj_of_eq σ ht z
  rw [hzt, ht] at h2
  obtain ⟨μ, hμ⟩ := exists_smul_eq_of_uTrans_one_eq h2.symm
  have h3 := uForm_mulVec σ z a v
  rw [hza, hμ, uForm_smul_right] at h3
  have hμ1 : μ = 1 := mul_right_cancel₀ hav (h3.trans (one_mul _).symm)
  rw [hμ, hμ1, one_smul]

theorem eq_one_of_mem_center_of_mulVec_eq_self [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a d : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    (G : SUGeomFacts σ a d) {z : SU σ m} (hz : z ∈ Subgroup.center (SU σ m))
    (hza : suMat σ m z *ᵥ a = a) : z = 1 := by
  have hzd : suMat σ m z *ᵥ d = d :=
    mulVec_eq_self_of_mem_center_of_uForm_ne_zero hσ hdd (by rw [had]; exact one_ne_zero) hz hza
  have hiso : ∀ e ∈ perpPair σ a d, uForm σ e e = 0 → suMat σ m z *ᵥ e = e := by
    intro e he hee
    have hde : uForm σ (d + e) (d + e) = 0 := by
      rw [uForm_add_left, uForm_add_right, uForm_add_right, hdd, hee, he.2,
        uForm_eq_zero_comm hσ he.2]
      simp
    have hade : uForm σ a (d + e) ≠ 0 := by
      rw [uForm_add_right, had, he.1, add_zero]
      exact one_ne_zero
    have h := mulVec_eq_self_of_mem_center_of_uForm_ne_zero hσ hde hade hz hza
    rw [mulVec_add, hzd] at h
    exact add_left_cancel h
  have hperp : ∀ w ∈ perpPair σ a d, suMat σ m z *ᵥ w = w := by
    intro w hw
    obtain ⟨e₁, he₁, e₂, he₂, he₁e₁, he₂e₂, rfl⟩ := G.sum hw
    rw [mulVec_add, hiso e₁ he₁ he₁e₁, hiso e₂ he₂ he₂e₂]
  refine eq_of_suMat_mulVec_eq fun u => ?_
  have hu : u = projPair σ a d u + uForm σ d u • a + uForm σ a u • d := by
    rw [projPair]
    abel
  rw [map_one, one_mulVec]
  conv_lhs => rw [hu]
  rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hza, hzd,
    hperp _ (projPair_mem hσ haa hdd had u)]
  exact hu.symm

theorem eq_one_of_mem_uRad_of_mem_isUTransGroup (hσ : ∀ c, σ (σ c) = c) {a d x : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    (G : SUGeomFacts σ a d) (hax : uForm σ a x = 0) (hx : ∀ c : F, x ≠ c • a)
    {X : Subgroup (SU σ m)} (hX : IsUTransGroup σ x X) {t : SU σ m} (ht : t ∈ X)
    (htu : t ∈ uRad σ a) : t = 1 := by
  have hp := projPair_mem hσ haa hdd had x
  have hp0 : projPair σ a d x ≠ 0 := by
    intro h0
    apply hx (uForm σ d x)
    rw [projPair, hax, zero_smul, sub_zero, sub_eq_zero] at h0
    exact h0
  obtain ⟨e, he, -, hep⟩ := G.nonorth hp hp0
  have hxe : uForm σ x e ≠ 0 := by
    rw [← uForm_conj σ hσ, ← uForm_projPair_of_mem_perpPair hσ he x]
    exact (map_ne_zero σ).2 hep
  obtain ⟨c, -, hc⟩ := (hX.1 t).1 ht
  obtain ⟨c', hc'⟩ := htu.2 e he.1
  rw [hc, uTrans_mulVec] at hc'
  have hcx : (c * uForm σ x e) • x = c' • a := add_left_cancel hc'
  by_cases hc0 : c = 0
  · apply suMat_injective σ
    rw [hc, hc0, uTrans_zero, map_one]
  · exfalso
    apply hx ((c * uForm σ x e)⁻¹ * c')
    rw [mul_smul, ← hcx, smul_smul, inv_mul_cancel₀ (mul_ne_zero hc0 hxe), one_smul]

theorem map_inf_map_uRad_eq_bot [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a d x : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    (G : SUGeomFacts σ a d) (hax : uForm σ a x = 0) (hx : ∀ c : F, x ≠ c • a)
    {X : Subgroup (SU σ m)} (hX : IsUTransGroup σ x X) {K : Type*} [Group K]
    {Φ : SU σ m →* K} (hker : Φ.ker ≤ Subgroup.center (SU σ m)) :
    X.map Φ ⊓ (uRad σ a).map Φ = ⊥ := by
  rw [eq_bot_iff]
  rintro k ⟨⟨t, ht, rfl⟩, ⟨u, hu, hut⟩⟩
  have hxa : uForm σ x a = 0 := uForm_eq_zero_comm hσ hax
  have hz : u⁻¹ * t ∈ Subgroup.center (SU σ m) := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hut, inv_mul_cancel])
  have hta : suMat σ m t *ᵥ a = a := by
    obtain ⟨c, -, hc⟩ := (hX.1 t).1 ht
    rw [hc, uTrans_mulVec, hxa, mul_zero, zero_smul, add_zero]
  have hza : suMat σ m (u⁻¹ * t) *ᵥ a = a := by
    rw [map_mul, ← mulVec_mulVec, hta]
    exact (inv_mem hu).1
  have htu : t = u := (inv_mul_eq_one.1
    (eq_one_of_mem_center_of_mulVec_eq_self hσ haa hdd had G hz hza)).symm
  rw [Subgroup.mem_bot, eq_one_of_mem_uRad_of_mem_isUTransGroup hσ haa hdd had G hax hx hX ht
    (by rw [htu]; exact hu), map_one]

end ModelRank

end CFSG.Timmesfeld.Transvection

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection.ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem conjSub_inf_pCoreOf_eq_bot_su [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {K : Type}
    [Group K] {Φ : SU σ m →* K} (hsurj : Function.Surjective Φ)
    (hker : Φ.ker ≤ Subgroup.center (SU σ m)) {a d : Fin m → F} {T : Subgroup (SU σ m)}
    (hT : IsUTransGroup σ a T) (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) (G : SUGeomFacts σ a d)
    (hcore : pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) =
      (uRad σ a).map Φ) {g : K}
    (hcent : conjSub (T.map Φ) g ≤ Subgroup.centralizer ((T.map Φ : Subgroup K) : Set K))
    (hne : conjSub (T.map Φ) g ≠ T.map Φ) :
    conjSub (T.map Φ) g ⊓ pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) =
      ⊥ := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  have ha : a ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  rw [hcore]
  obtain ⟨γ, rfl⟩ := hsurj g
  rw [conjSub_map] at hcent hne ⊢
  have hx0 : suMat σ m γ *ᵥ a ≠ 0 := suMat_mulVec_ne_zero σ γ ha
  have hxx : uForm σ (suMat σ m γ *ᵥ a) (suMat σ m γ *ᵥ a) = 0 :=
    (uForm_mulVec σ γ a a).trans haa
  have hTx := hT.conjSub γ
  have hxa' : ∀ c : F, suMat σ m γ *ᵥ a ≠ c • a := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hx0 hc
    rw [hc] at hTx
    exact hne (by rw [(hTx.of_smul hσ hc0).eq hT])
  have hcomm : Commuting ((conjSub T γ).map Φ) (T.map Φ) :=
    fun k hk l hl => (Subgroup.mem_centralizer_iff.1 (hcent hk) l hl).symm
  have hax : uForm σ a (suMat σ m γ *ᵥ a) = 0 := by
    rcases hTx.uForm_eq_zero_of_center hσ one_ne_zero h1 hT hx0 hxx haa
        (commutator_mem_center hker hcomm) with h | ⟨l, hl⟩
    · exact uForm_eq_zero_comm hσ h
    · exfalso
      have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hl
        exact ha hl
      refine hxa' l⁻¹ ?_
      conv_rhs => rw [hl]
      rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
  exact map_inf_map_uRad_eq_bot hσ haa hdd had G hax hxa' hTx hker

theorem exists_conjSub_not_commute_su [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {K : Type} [Group K] {Φ : SU σ m →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ m)) {a d : Fin m → F} {T : Subgroup (SU σ m)}
    (hT : IsUTransGroup σ a T) (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0)
    (had : uForm σ a d = 1) (G : SUGeomFacts σ a d)
    (hcore : pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) =
      (uRad σ a).map Φ) :
    ∃ g : K, conjSub (T.map Φ) g ≤ Subgroup.centralizer ((T.map Φ : Subgroup K) : Set K) ∧
      conjSub (T.map Φ) g ≠ T.map Φ ∧
      ∃ x ∈ pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)),
        ∃ t ∈ conjSub (T.map Φ) g, x * t ≠ t * x := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  have ha : a ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  have hda : uForm σ d a = 1 := uForm_swap_eq_one hσ had
  rw [hcore]
  obtain ⟨e, he, he0, hee⟩ := G.exists_iso
  obtain ⟨f, hf, hff, hef⟩ := G.partner he he0 hee
  have hfe : uForm σ f e = 1 := uForm_swap_eq_one hσ hef
  have hfa : uForm σ f a = 0 := uForm_eq_zero_comm hσ hf.1
  have hea : uForm σ e a = 0 := uForm_eq_zero_comm hσ he.1
  have hvv : uForm σ (d + f) (d + f) = 0 := by
    rw [uForm_add_left, uForm_add_right, uForm_add_right, hdd, hff, hf.2,
      uForm_eq_zero_comm hσ hf.2]
    simp
  have hav : uForm σ a (d + f) = 1 := by rw [uForm_add_right, had, hf.1, add_zero]
  have hve : uForm σ (d + f) e = 1 := by rw [uForm_add_left, he.2, hfe, zero_add]
  obtain ⟨γ₁, hγ₁⟩ := exists_suMat_mulVec_eq hσ haa hvv (by rw [hav]; exact one_ne_zero)
    (by rw [hav]; exact h1)
  obtain ⟨γ₂, hγ₂⟩ := exists_suMat_mulVec_eq hσ hvv hee (by rw [hve]; exact one_ne_zero)
    (by rw [hve]; exact h1)
  have hγ : suMat σ m (γ₂ * γ₁) *ᵥ a = e := by rw [map_mul, ← mulVec_mulVec, hγ₁, hγ₂]
  have hTe : IsUTransGroup σ e (conjSub T (γ₂ * γ₁)) := by
    have h := hT.conjSub (γ₂ * γ₁)
    rwa [hγ] at h
  obtain ⟨z, hz, hzd⟩ := exists_mem_uRad_mulVec_d_eq_add hσ haa had hf hff
  obtain ⟨c, hc⟩ := hz.2 e he.1
  have hc1 : c = 1 := by
    have h2 := uForm_mulVec σ z d e
    rw [hzd, hc, uForm_add_left, uForm_add_right, uForm_add_right, uForm_smul_right,
      uForm_smul_right, he.2, hda, hfe, hfa] at h2
    linear_combination h2 - (CharTwo.two_eq_zero : (2 : F) = 0)
  obtain ⟨t₀, ht₀⟩ := hTe.2 1 h1
  have ht₀T : t₀ ∈ conjSub T (γ₂ * γ₁) := (hTe.1 t₀).2 ⟨1, h1, ht₀⟩
  refine ⟨Φ (γ₂ * γ₁), ?_, ?_, Φ z, ⟨z, hz, rfl⟩, Φ t₀, ?_, ?_⟩
  ·
    rw [conjSub_map]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (commuting_map Φ (hTe.commuting hσ hT hea) k hk l hl).eq.symm
  ·
    rw [conjSub_map]
    intro hmap
    obtain ⟨l, hl⟩ := suMapEqStmt_holds hσ htr hker hT hTe ha he0 haa hee hmap.symm
    have h2 := he.2
    rw [hl, uForm_smul_right, hda, mul_one] at h2
    exact he0 (by rw [hl, h2, zero_smul])
  · rw [conjSub_map]
    exact ⟨t₀, ht₀T, rfl⟩
  ·
    intro hcomm
    have hw : z * t₀ * z⁻¹ * t₀⁻¹ ∈ Subgroup.center (SU σ m) := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group)
    have ht₀a : suMat σ m t₀ *ᵥ a = a := by
      rw [ht₀, uTrans_mulVec, hea, mul_zero, zero_smul, add_zero]
    have ht₀a' : suMat σ m t₀⁻¹ *ᵥ a = a := by
      rw [suMat_inv_of_eq hee ht₀, uTrans_mulVec, hea, mul_zero, zero_smul, add_zero]
    have hwa : suMat σ m (z * t₀ * z⁻¹ * t₀⁻¹) *ᵥ a = a := by
      rw [map_mul, map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ht₀a',
        (inv_mem hz).1, ht₀a, hz.1]
    have h4 : z * t₀ * z⁻¹ = t₀ :=
      mul_inv_eq_one.1 (eq_one_of_mem_center_of_mulVec_eq_self hσ haa hdd had G hw hwa)
    have h5 := suMat_conj_of_eq σ ht₀ z
    rw [h4, ht₀, hc, hc1, one_smul] at h5
    obtain ⟨μ, hμ⟩ := exists_smul_eq_of_uTrans_one_eq h5.symm
    have h6 := congrArg (uForm σ d) hμ
    rw [uForm_add_right, uForm_smul_right, he.2, hda, mul_zero, zero_add] at h6
    exact one_ne_zero h6

end CFSG.RankThree.GF2n.Tim79a
