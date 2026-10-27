module

public import CFSG.Quasithin.Background.S1549CFDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem claim_f_Egamma (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G}
    (hH : Adm T Mc M H)
    (h98 : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    (hc : ClaimC T M V₁ H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g) :
    ⁅F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G), VH T M H⁆ = ⊥ := by
  have hF91 := cx.hF91 h113 hH
  have hQ := hF91.pCoreOf_eq_centralizerMod
  have hVγH := h98.Vγ_le_H s
  have hVγab := h98.isElemAbelian_Vγ (g := g)
  have hEQ : F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G) ≤ pCoreOf 2 H := by
    intro e he
    rw [hQ]
    exact ⟨hVγH he.1, he.2.1, he.2.2⟩
  have hEΩ : F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G) ≤
      omegaOneOf (pCoreOf 2 H) := fun e he =>
    Subgroup.subset_closure ⟨hEQ he, isElemAbelian_pow_eq_one hVγab he.1⟩
  have hEU : ∀ e ∈ F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G),
      ∀ u ∈ conjClosure (ZS153 T M V₁) H, e * u = u * e := fun e he u hu =>
    Subgroup.mem_centralizer_iff.mp (hc.2 hu).2 e (hEΩ he)
  have hVHN : conjClosure (VZ T M) H ≤ Subgroup.normalizer (F8.Uγ (VZ T M) H (g : G) : Set G) :=
    le_normalizer_of_commutator_le
      ((h98.F913_3 s (X := VZ T M) (Y := VZ T M) (Or.inr rfl) (Or.inr rfl)).trans inf_le_right)
  have key : ∀ k ∈ H, ∀ e ∈ F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G),
      ∀ v ∈ conjSub k (VZ T M), v * e = e * v := by
    intro k hk e he v hv
    by_contra hne
    have hkinv : k⁻¹ ∈ H := H.inv_mem hk
    have hv' : k⁻¹ * v * k ∈ VZ T M := mem_conjSub.mp hv
    have he'W : k⁻¹ * e * k ∈ conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G)) := by
      simpa using mul_mem_conjSub (g := k⁻¹) he.1
    have he'Zs : k⁻¹ * e * k ∈ Subgroup.centralizer (ZS153 T M V₁ : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      have h1 := hEU e he (k * z * k⁻¹) (mem_conjClosure hk hz)
      calc z * (k⁻¹ * e * k) = k⁻¹ * ((k * z * k⁻¹) * e) * k := by group
        _ = k⁻¹ * (e * (k * z * k⁻¹)) * k := by rw [h1]
        _ = (k⁻¹ * e * k) * z := by group
    have hne' : ⁅VZ T M, Subgroup.zpowers (k⁻¹ * e * k)⁆ ≠ ⊥ := by
      intro hbot
      apply hne
      have h1 : ⁅k⁻¹ * v * k, k⁻¹ * e * k⁆ ∈ ⁅VZ T M, Subgroup.zpowers (k⁻¹ * e * k)⁆ :=
        Subgroup.commutator_mem_commutator hv' (Subgroup.mem_zpowers _)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact (inv_conj_comm_iff k v e).mp h1
    have hWab : IsElemAbelian 2 (conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G))) :=
      isElemAbelian_conjSub hVγab
    have hVHW : conjClosure (VZ T M) H ≤
        Subgroup.normalizer (conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G)) : Set G) := by
      have := conjSub_le_normalizer (g := k⁻¹) hVHN
      rwa [F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure _ H hkinv)] at this
    have hcommW : ⁅VZ T M, Subgroup.zpowers (k⁻¹ * e * k)⁆ ≤
        conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G)) := by
      refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      have hyW : y ∈ conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G)) :=
        (Subgroup.zpowers_le.mpr he'W) hy
      have hxN := (Subgroup.mem_normalizer_iff.mp (hVHW (le_conjClosure _ H hx)) y).mp hyW
      rw [commutatorElement_def]
      exact (conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G))).mul_mem hxN
        ((conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G))).inv_mem hyW)
    rcases cx.r47 (k⁻¹ * e * k) he'Zs with hb | hr
    · exact hne' hb
    · have hy : ∀ y : G, conjSub y (VZ T M) ≤ conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G)) →
          conjSub y (VZ T M) ≤ Subgroup.centralizer (VZ T M : Set G) := by
        intro y hy
        have hnorm : conjSubgroup (VZ T M) y⁻¹ ≤
            Subgroup.normalizer ((⁅VZ T M, Subgroup.zpowers (k⁻¹ * e * k)⁆ : Subgroup G) : Set G) := by
          rw [← conjSub_inv_eq_conjSubgroup, inv_inv]
          intro w hw
          refine Subgroup.centralizer_le_normalizer _ ?_
          refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
          exact isElemAbelian_comm hWab (hcommW hc) (hy hw)
        have := hr y⁻¹ hnorm
        rwa [← conjSub_inv_eq_conjSubgroup, inv_inv] at this
      have hWC : conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G)) ≤ Subgroup.centralizer (VZ T M : Set G) := by
        have hWeq : conjSub k⁻¹ (F8.Uγ (VZ T M) H (g : G)) =
            conjSub (k⁻¹ * (g : G)) (conjClosure (VZ T M) H) := by
          unfold F8.Uγ; rw [conjSub_mul]
        rw [hWeq, conjSub_le_iff]
        refine conjClosure_le fun h hh z hz => ?_
        rw [mem_conjSub, inv_inv]
        have hle : conjSub (k⁻¹ * (g : G) * h) (VZ T M) ≤
            conjSub (k⁻¹ * (g : G)) (conjClosure (VZ T M) H) := by
          rw [conjSub_mul]
          exact conjSub_mono _ (HypF91.conjSub_le_conjClosure hh)
        have hmem := hy (k⁻¹ * (g : G) * h) (hWeq ▸ hle) (mul_mem_conjSub hz)
        have e : (k⁻¹ * (g : G) * h) * z * (k⁻¹ * (g : G) * h)⁻¹ =
            (k⁻¹ * (g : G)) * (h * z * h⁻¹) * (k⁻¹ * (g : G))⁻¹ := by group
        rwa [e] at hmem
      have hcomm := Subgroup.mem_centralizer_iff.mp (hWC he'W) (k⁻¹ * v * k) hv'
      exact hne ((inv_conj_comm_iff k v e).mp hcomm)
  have hEV : ∀ e ∈ F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G),
      ∀ x ∈ conjClosure (VZ T M) H, x * e = e * x := by
    intro e he x hx
    have : conjClosure (VZ T M) H ≤ Subgroup.centralizer ({e} : Set G) := by
      refine conjClosure_le fun h hh z hz => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (key h hh e he _ (mul_mem_conjSub hz)).symm
    exact ((Subgroup.mem_centralizer_iff.mp (this hx)) e rfl).symm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro e he
  exact Subgroup.mem_centralizer_iff.mpr fun x hx => hEV e he x hx

theorem claim_g (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G}
    (hH : Adm T Mc M H)
    (h98 : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    (hc : ClaimC T M V₁ H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g) :
    F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G) <
      F8.Uγ (ZS153 T M V₁) H (g : G) := by
  have hf := claim_f_Egamma h113 cx hH h98 hc s
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hEq => ?_
  apply h98.F913_5a s
  have hDE : F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G) ≤
      F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G) :=
    centralizerMod_mono_left _ h98.Uγ_le_Vγ
  have hbot : ⁅F8.Uγ (ZS153 T M V₁) H (g : G), VZ T M⁆ = ⊥ := by
    rw [← hEq]
    refine le_bot_iff.mp ?_
    rw [← hf]
    exact Subgroup.commutator_mono hDE (le_conjClosure _ H)
  rw [hbot]
  exact bot_le

theorem claim_f_EH (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G}
    (hH : Adm T Mc M H)
    (h98 : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    (hc : ClaimC T M V₁ H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g) :
    ⁅F9.EH (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G),
      F8.Uγ (VZ T M) H (g : G)⁆ = ⊥ := by
  have hlt := claim_g h113 cx hH h98 hc s
  obtain ⟨δ, δ', k, y, sk, hy1, hy2, eU, eB, -, -⟩ :=
    h98.exists_symmetric_setup s (h98.not_Vγ_le_ballStab_of_lt s hlt)
  have hf := claim_f_Egamma h113 cx hH h98 hc sk
  have hyp := h98.amalgamHypV
  have hyg : (y : G) * (g : G) ∈ H := by
    have h1 : (y * g) • F8.γ₁ T (Y153 Mc M) H = F8.γ₁ T (Y153 Mc M) H := by
      rw [mul_smul, s.edge₁, hy1]
    have := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hyp.le₂] at this
    simpa using this
  have hky : (k : G)⁻¹ * (y : G) ∈ H := by
    have h1 : (k⁻¹ * y) • F8.γ₁ T (Y153 Mc M) H = F8.γ₁ T (Y153 Mc M) H := by
      rw [mul_smul, hy2, ← sk.edge₁, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hyp.le₂] at this
    simpa using this
  have eVg : conjSub (y : G) (F8.Uγ (VZ T M) H (g : G)) = conjClosure (VZ T M) H := by
    rw [F8.Uγ, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer
      (le_normalizer_conjClosure _ H hyg)]
  have eVk : conjSub (y : G) (conjClosure (VZ T M) H) = F8.Uγ (VZ T M) H (k : G) := by
    have e : (y : G) = (k : G) * ((k : G)⁻¹ * (y : G)) := by group
    rw [F8.Uγ, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer
      (le_normalizer_conjClosure _ H hky)]
  have eA : conjSub (y : G) (F8.A₁ (quasithinOmegaOneCenter T) (g : G)) =
      quasithinOmegaOneCenter T := by
    rw [F8.A₁, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer (h98.H_normalizes_V₁ hyg)]
  have hEH : conjSub (y : G)
      (F9.EH (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) =
      F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (k : G) := by
    rw [F9.EH, F9.Eγ, conjSub_centralizerMod, eA, eB, eVk]
  have h2 : ⁅conjSub (y : G)
      (F9.EH (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)),
      conjSub (y : G) (F8.Uγ (VZ T M) H (g : G))⁆ = ⊥ := by
    rw [hEH, eVg]; exact hf
  rwa [conjSub_commutator, conjSub_eq_bot_iff] at h2

theorem claim_rk_Ustar {H : Subgroup G}
    (h98 : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g) :
    rk (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) =
      mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) :=
  h98.rk_autOn_tilde_Uγ s

theorem claim_h_chain (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G}
    (hH : Adm T Mc M H)
    (h98 : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    (hc : ClaimC T M V₁ H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
      (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)))
    (hle : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
      mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G))) :
    letI : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)) :=
      commGroupOfElemAbelian (h98.toHypF91.isElemAbelian_tilde)
    autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)) ≤
      autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (VZ T M) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)) ∧
    rkIdx (fixV (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (VZ T M) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)))) ≤
      mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ∧
    mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
      rk (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ∧
    rk (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ≤
      rk (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (VZ T M) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ∧
    rkIdx (fixV (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)))) ≤
      rk (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) := by
  have _ := hpos
  have hf1 := claim_f_EH h113 cx hH h98 hc s
  have hF91 := h98.toHypF91
  have hUγH := h98.Uγ_le_H s
  have hVγH := h98.Vγ_le_H s
  have hUV := h98.Uγ_le_Vγ (g := g)
  have hVp : IsPGroup 2 (F8.Uγ (VZ T M) H (g : G)) :=
    isPGroup_of_isElemAbelian (h98.isElemAbelian_Vγ (g := g))
  have hDU := DH_le_centralizerMod_of_EH h98 hUV hf1
  have hDV := DH_le_centralizerMod_of_EH h98 (le_refl _) hf1
  have h3 : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
      rk (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) :=
    hle.trans_eq (claim_rk_Ustar h98 s).symm
  exact ⟨autOn_le_autOn _ (secImg_mono hUV),
    (rkIdx_fixV_autOn_tilde hF91 hVγH).le.trans (mIdx_anti_right hDV), h3,
    ((rk_autOn_tilde hF91 hUγH).le.trans (mIdx_inf_le_of_le hVp hUV)).trans
      (rk_autOn_tilde hF91 hVγH).ge,
    ((rkIdx_fixV_autOn_tilde hF91 hUγH).le.trans (mIdx_anti_right hDU)).trans h3⟩

theorem claim_h_full (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G}
    (hH : Adm T Mc M H)
    (h98 : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    (hc : ClaimC T M V₁ H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
      (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)))
    (hle : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
      mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G))) :
    letI : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)) :=
      commGroupOfElemAbelian (h98.toHypF91.isElemAbelian_tilde)
    (IsA2 (autOn (tildeOf (quasithinOmegaOneCenter T) H)
          (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)))
        (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
          (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ∧
      IsQuadratic (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ∧
      rAV (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ≤ 1) ∧
    (IsA2 (autOn (tildeOf (quasithinOmegaOneCenter T) H)
          (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)))
        (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (VZ T M) H (g : G)))
          (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ∧
      IsQuadratic (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (VZ T M) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ∧
      rAV (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (VZ T M) H (g : G)))
        (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ≤ 1) := by
  obtain ⟨-, h2, h3, h4, h5⟩ := claim_h_chain h113 cx hH h98 hc s hpos hle
  have hF91 := h98.toHypF91
  have hUγH := h98.Uγ_le_H s
  have hVγH := h98.Vγ_le_H s
  have hUV := h98.Uγ_le_Vγ (g := g)
  have hUab := h98.isElemAbelian_Uγ (g := g)
  have hVab := h98.isElemAbelian_Vγ (g := g)
  have hnt : ¬ F8.Uγ (ZS153 T M V₁) H (g : G) ≤ pCoreOf 2 H := by
    intro hle'
    have hEq : F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G) =
        F8.Uγ (ZS153 T M V₁) H (g : G) := by
      rw [h98.Dγ_eq_inf_pCoreOf s]; exact inf_eq_left.mpr hle'
    have h1 : (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)).relIndex
        (F8.Uγ (ZS153 T M V₁) H (g : G)) = 1 := Subgroup.relIndex_eq_one.mpr hEq.ge
    unfold mIdx at hpos
    rw [h1] at hpos
    simp at hpos
  have hnt' : ¬ F8.Uγ (VZ T M) H (g : G) ≤ pCoreOf 2 H := fun h => hnt (hUV.trans h)
  have hqU := commutator_commutator_mem_of_abelian (N := quasithinOmegaOneCenter T) hUab
    ((h98.F913_3 s (X := ZS153 T M V₁) (Y := ZS153 T M V₁) (Or.inl rfl) (Or.inl rfl)).trans
      inf_le_right)
  have hqV := commutator_commutator_mem_of_abelian (N := quasithinOmegaOneCenter T) hVab
    ((h98.F913_3 s (X := ZS153 T M V₁) (Y := VZ T M) (Or.inl rfl) (Or.inr rfl)).trans
      inf_le_right)
  exact ⟨⟨isA2_autOn_tilde hF91 hUγH hUab hnt, isQuadratic_autOn_tilde hF91 hqU,
      @rAV_le_one_of_rkIdx_le _ (commGroupOfElemAbelian hF91.isElemAbelian_tilde) _ h5⟩,
    ⟨isA2_autOn_tilde hF91 hVγH hVab hnt', isQuadratic_autOn_tilde hF91 hqV,
      @rAV_le_one_of_rkIdx_le _ (commGroupOfElemAbelian hF91.isElemAbelian_tilde) _
        (h2.trans (h3.trans h4))⟩⟩

theorem claim_h_isA2 (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G}
    (hH : Adm T Mc M H)
    (h98 : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    (hc : ClaimC T M V₁ H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
      (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)))
    (hle : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
      mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G))) :
    letI : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)) :=
      commGroupOfElemAbelian (h98.toHypF91.isElemAbelian_tilde)
    IsA2 (autOn (tildeOf (quasithinOmegaOneCenter T) H)
          (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)))
        (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (ZS153 T M V₁) H (g : G)))
          (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) ∧
      IsA2 (autOn (tildeOf (quasithinOmegaOneCenter T) H)
          (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)))
        (autOn (tildeOf (quasithinOmegaOneCenter T) (F8.Uγ (VZ T M) H (g : G)))
          (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))) := by
  obtain ⟨⟨h1, -, -⟩, h2, -, -⟩ := claim_h_full h113 cx hH h98 hc s hpos hle
  exact ⟨h1, h2⟩

theorem exists_good_setup (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t)
    {H : Subgroup G} (hH : Adm T Mc M H)
    (h98 : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    (hc : ClaimC T M V₁ H) :
    ∃ (γ γ' : F8.Geom T (Y153 Mc M) H) (g : ↥(((Y153 Mc M) ⊔ T) ⊔ H))
      (_ : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g),
      0 < mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ∧
      mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
        mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
          (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) := by
  obtain ⟨γ, γ', g, s⟩ := h98.exists_F8Setup
  have hlt := claim_g h113 cx hH h98 hc s
  obtain ⟨δ, δ', k, sk, hpos, hle, -⟩ := h98.F916_4 s hlt
  exact ⟨δ, δ', k, sk, hpos, hle⟩

end S1549C

end CFSG.Quasithin
