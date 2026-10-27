module

public import CFSG.Quasithin.AppendixH.H16.OctadZSpaces
public import CFSG.Quasithin.AppendixH.H16.OctadZGroup
public import CFSG.Quasithin.AppendixH.H16.OctadZBridge
public import CFSG.Quasithin.AppendixH.H16.OctadTransv
public import CFSG.Quasithin.AppendixH.Common.OctadCentralizer

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

private theorem rho_mem_octV5 {γ : ↥AutPerm} (hγ : (γ : S24) ∈ octStab octad0) {y : W11}
    (hy : y ∈ octV5) : rhoC11 AutPerm le_rfl γ y ∈ octV5 :=
  isActsInv_octV5 (fun v => rhoC11 AutPerm le_rfl γ v)
    ⟨rhoC11 AutPerm le_rfl γ, rhoCd_mem_imgCd γ.2 hγ, rfl⟩ y hy

private theorem mem_cenM_iff {V : Type*} [CommGroup V] (ρ : ↥AutPerm →* MulAut V)
    (W : Subgroup V) (γ : ↥AutPerm) :
    γ ∈ cenM (Γ := AutPerm) ρ W ↔ ∀ x ∈ W, ρ γ x = x := by
  rw [show cenM (Γ := AutPerm) ρ W = (centSub W).comap ρ from rfl, Subgroup.mem_comap,
    mem_centSub]

theorem eq_one_of_fix_octV5 (γ : ↥AutPerm)
    (hγ : (γ : S24) ∈ octStab octad0) (h : ∀ x ∈ octV5, rhoC11 AutPerm le_rfl γ x = x) :
    (γ : S24) = 1 := by
  have hcomm : ∀ k ∈ fixO, k * (γ : S24) = (γ : S24) * k := by
    intro k hk
    have hk_aut : k ∈ AutPerm := (fixO_le_octStab_octad0.trans octStab_octad0_le_AutPerm) hk
    have hk_stab : k ∈ octStab octad0 := fixO_le_octStab_octad0 hk
    set c : S24 := (γ : S24) * k * (γ : S24)⁻¹ * k⁻¹ with hc
    have hc_fixO : c ∈ fixO := by
      have hmem : (⟨k, hk_stab⟩ : ↥(octStab octad0)) ∈
          (octFix octad0).subgroupOf (octStab octad0) :=
        Subgroup.mem_subgroupOf.2 (by rw [octFix_octad0]; exact hk)
      have hconj : (γ : S24) * k * (γ : S24)⁻¹ ∈ fixO := by
        have h1 := (normal_octFix octad0).conj_mem (⟨k, hk_stab⟩ : ↥(octStab octad0)) hmem
          (⟨(γ : S24), hγ⟩ : ↥(octStab octad0))
        have h2 := Subgroup.mem_subgroupOf.1 h1
        rw [octFix_octad0] at h2
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h2
      rw [hc]
      exact fixO.mul_mem hconj (fixO.inv_mem hk)
    have hc_aut : c ∈ AutPerm := (fixO_le_octStab_octad0.trans octStab_octad0_le_AutPerm) hc_fixO
    have hfixc : ∀ x ∈ octV5, rhoC11 AutPerm le_rfl ⟨c, hc_aut⟩ x = x := by
      intro x hx
      have hc_eq : (⟨c, hc_aut⟩ : ↥AutPerm) = γ * ⟨k, hk_aut⟩ * γ⁻¹ * ⟨k, hk_aut⟩⁻¹ := by
        apply Subtype.ext
        simp [hc, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hc_eq]
      simp only [map_mul, map_inv]
      set A : MulAut W11 := rhoC11 AutPerm le_rfl γ with hA
      set K : MulAut W11 := rhoC11 AutPerm le_rfl ⟨k, hk_aut⟩ with hK
      have hKx : K⁻¹ x ∈ octV5 := by
        rw [hK, ← map_inv]
        exact rho_mem_octV5 (by simpa using (octStab octad0).inv_mem hk_stab) hx
      have hAinv : A⁻¹ (K⁻¹ x) = K⁻¹ x := by
        have hfix := h (K⁻¹ x) hKx
        rw [hA] at hfix
        calc A⁻¹ (K⁻¹ x) = A⁻¹ (A (K⁻¹ x)) := by rw [hfix]
          _ = K⁻¹ x := MulAut.inv_apply_self W11 A (K⁻¹ x)
      simp only [MulAut.mul_apply]
      rw [hAinv, MulAut.apply_inv_self W11]
      rw [hA]
      exact h x hx
    obtain ⟨t, ht⟩ := (mem_fixO_iff c).1 hc_fixO
    have ht0 : t = 0 := by
      apply ko11_eq_one_of_fix_V5 t
      intro x hx
      have hfixx := hfixc x hx
      have hc_eq : (⟨c, hc_aut⟩ : ↥AutPerm) = ⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩ :=
        Subtype.ext ht
      rw [hc_eq] at hfixx
      exact hfixx
    have hc1 : c = 1 := by rw [ht, ht0, koPerm_zero]
    have hconj : (γ : S24) * k * (γ : S24)⁻¹ = k := by
      have h1 : c = 1 := hc1
      rw [hc] at h1
      exact mul_inv_eq_one.mp h1
    have hcommk : k * (γ : S24) = (γ : S24) * k := by
      conv_lhs => rw [← hconj]
      group
    exact hcommk
  have hcent : (γ : S24) ∈ Subgroup.centralizer (fixO : Set S24) := by
    rw [Subgroup.mem_centralizer_iff]
    exact hcomm
  have hmem : (γ : S24) ∈ octStab octad0 ⊓ Subgroup.centralizer (fixO : Set S24) :=
    Subgroup.mem_inf.mpr ⟨hγ, hcent⟩
  rw [← octFix_octad0] at hmem
  rw [octStab_inf_centralizer_octFix isOctad_octad0, octFix_octad0] at hmem
  obtain ⟨t, ht⟩ := (mem_fixO_iff (γ : S24)).1 hmem
  have ht0 : t = 0 := by
    apply ko11_eq_one_of_fix_V5 t
    intro x hx
    have hfixx := h x hx
    have hγeq : γ = (⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩ : ↥AutPerm) := Subtype.ext ht
    rw [hγeq] at hfixx
    exact hfixx
  rw [ht, ht0, koPerm_zero]

theorem rhoC11_dPerm_fix_octVz (u : Fin 16) {x : W11} (hx : x ∈ octVz) :
    rhoC11 AutPerm le_rfl ⟨dPerm u, dPerm_mem_M24g u⟩ x = x := by
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hx
  rw [rhoC11_dPerm, dArr_fix_vz u u.2 m hm]

private theorem card_cenM_octVz_le :
    Nat.card ↥(cenM (Γ := AutPerm) (rhoC11 AutPerm le_rfl) octVz) ≤ 16 := by
  classical
  let ρ : ↥AutPerm →* MulAut W11 := rhoC11 AutPerm le_rfl
  let e : W11 := toW 11 1024
  have psi_mem : ∀ γ : ↥(cenM (Γ := AutPerm) ρ octVz), ρ γ.1 e * e⁻¹ ∈ octVz := by
    intro γ
    have hγmem : ∀ u ∈ octVz, ρ γ.1 u = u := (mem_cenM_iff ρ octVz γ.1).1 γ.2
    have hγst : (γ.1 : S24) ∈ octStab octad0 :=
      mem_octStab_of_fixes_three γ.1 (hγmem _ toW_three_mem_octVz)
    have he5 : e ∈ octV5 := by
      change toW 11 1024 ∈ octV5
      exact toW_1024_mem_octV5
    have hy5 : ρ γ.1 e ∈ octV5 :=
      isActsInv_octV5 (fun v => ρ γ.1 v)
        ⟨ρ γ.1, rhoCd_mem_imgCd γ.1.2 hγst, rfl⟩ e he5
    have hyV5 : ρ γ.1 e * e⁻¹ ∈ octV5 := octV5.mul_mem hy5 (octV5.inv_mem he5)
    rcases mem_octV5_split hyV5 with h | h
    · exact h
    · exfalso
      change (ρ γ.1 e * e⁻¹) * e ∈ octVz at h
      have hz : ρ γ.1 e ∈ octVz := by
        rw [mul_assoc, inv_mul_cancel, mul_one] at h
        exact h
      have hγinv_fix : ρ γ.1⁻¹ (ρ γ.1 e) = ρ γ.1 e :=
        (mem_cenM_iff ρ octVz γ.1⁻¹).1 ((cenM (Γ := AutPerm) ρ octVz).inv_mem γ.2) _ hz
      have h1 : ρ γ.1⁻¹ (ρ γ.1 e) = e := by
        rw [map_inv]
        exact MulAut.inv_apply_self W11 (ρ γ.1) e
      have he_eq : e = ρ γ.1 e := h1.symm.trans hγinv_fix
      apply toW_1024_not_mem_octVz
      change e ∈ octVz
      rw [he_eq]
      exact hz
  let ψ : ↥(cenM (Γ := AutPerm) ρ octVz) → ↥octVz := fun γ => ⟨ρ γ.1 e * e⁻¹, psi_mem γ⟩
  have psi_inj : Function.Injective ψ := by
    intro γ δ hγδ
    have hγmem : ∀ u ∈ octVz, ρ γ.1 u = u := (mem_cenM_iff ρ octVz γ.1).1 γ.2
    have hδmem : ∀ u ∈ octVz, ρ δ.1 u = u := (mem_cenM_iff ρ octVz δ.1).1 δ.2
    have heq : ρ γ.1 e = ρ δ.1 e := by
      have h := congrArg Subtype.val hγδ
      exact mul_right_cancel h
    let ξ : ↥AutPerm := δ.1⁻¹ * γ.1
    have hξH : ξ ∈ cenM (Γ := AutPerm) ρ octVz :=
      (cenM (Γ := AutPerm) ρ octVz).mul_mem
        ((cenM (Γ := AutPerm) ρ octVz).inv_mem δ.2) γ.2
    have hξmem : ∀ u ∈ octVz, ρ ξ u = u := (mem_cenM_iff ρ octVz ξ).1 hξH
    have hξst : (ξ : S24) ∈ octStab octad0 :=
      mem_octStab_of_fixes_three ξ (hξmem _ toW_three_mem_octVz)
    have hξfixe : ρ ξ e = e := by
      change ρ (δ.1⁻¹ * γ.1) e = e
      rw [map_mul, MulAut.mul_apply, heq, map_inv]
      exact MulAut.inv_apply_self W11 (ρ δ.1) e
    have hξfixV5 : ∀ x ∈ octV5, ρ ξ x = x := by
      intro x hx
      rcases mem_octV5_split hx with hx' | hx'
      · exact hξmem x hx'
      · calc ρ ξ x = ρ ξ ((x * e) * e⁻¹) := by rw [mul_inv_cancel_right x e]
          _ = ρ ξ (x * e) * ρ ξ e⁻¹ := by rw [map_mul]
          _ = (x * e) * (ρ ξ e)⁻¹ := by rw [hξmem (x * e) hx', map_inv]
          _ = (x * e) * e⁻¹ := by rw [hξfixe]
          _ = x := mul_inv_cancel_right x e
    have hξ1 : (ξ : S24) = 1 := eq_one_of_fix_octV5 ξ hξst hξfixV5
    have hξval : (ξ : S24) = (δ.1 : S24)⁻¹ * (γ.1 : S24) := by
      simp [ξ, Subgroup.coe_mul, Subgroup.coe_inv]
    have hγδ' : (γ.1 : S24) = (δ.1 : S24) := by
      have h : (δ.1 : S24)⁻¹ * (γ.1 : S24) = 1 := hξval ▸ hξ1
      calc (γ.1 : S24) = (δ.1 : S24) * ((δ.1 : S24)⁻¹ * (γ.1 : S24)) := by group
        _ = (δ.1 : S24) * 1 := by rw [h]
        _ = (δ.1 : S24) := mul_one _
    exact Subtype.ext (Subtype.ext hγδ')
  have hcard := Nat.card_le_card_of_injective ψ psi_inj
  rw [card_octVz] at hcard
  exact hcard

private theorem cenM_octVz_aux :
    cenM (Γ := AutPerm) (rhoC11 AutPerm le_rfl) octVz = dGrp.subgroupOf AutPerm := by
  have hle : dGrp.subgroupOf AutPerm ≤ cenM (Γ := AutPerm) (rhoC11 AutPerm le_rfl) octVz := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨u, hu⟩ := mem_dGrp_iff.mp hg
    rw [mem_cenM_iff]
    intro x hx
    have hg' : g = (⟨dPerm u, dPerm_mem_M24g u⟩ : ↥AutPerm) := Subtype.ext hu.symm
    rw [hg']
    exact rhoC11_dPerm_fix_octVz u hx
  have hcard : Nat.card ↥(cenM (Γ := AutPerm) (rhoC11 AutPerm le_rfl) octVz) ≤
      Nat.card ↥(dGrp.subgroupOf AutPerm) := by
    have h2 : Nat.card ↥(dGrp.subgroupOf AutPerm) = 16 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe dGrp_le_M24g).toEquiv).trans card_dGrp
    have h1 := card_cenM_octVz_le
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem mem_dGrp_of_fix_octVz (γ : ↥M24g)
    (h : ∀ x ∈ octVz, rhoC11 AutPerm le_rfl γ x = x) : (γ : S24) ∈ dGrp := by
  let γA : ↥AutPerm := ⟨γ.1, γ.2⟩
  have hH : γA ∈ cenM (Γ := AutPerm) (rhoC11 AutPerm le_rfl) octVz :=
    (mem_cenM_iff (rhoC11 AutPerm le_rfl) octVz γA).2 h
  have hH' : γA ∈ dGrp.subgroupOf AutPerm := by rwa [cenM_octVz_aux] at hH
  have hmem : (γA : S24) ∈ dGrp := Subgroup.mem_subgroupOf.1 hH'
  simpa using hmem

theorem cenM_octVz :
    cenM (Γ := M24g) (rhoC11 AutPerm le_rfl) octVz = dGrp.subgroupOf M24g := by
  exact cenM_octVz_aux

theorem cenMS_octVz :
    (cenM (Γ := M24g) (rhoC11 AutPerm le_rfl) octVz).map M24g.subtype = dGrp := by
  rw [cenM_octVz, Subgroup.map_subgroupOf_eq_of_le dGrp_le_M24g]

theorem cenM_octWz :
    cenM (Γ := M24g) (rhoC11 AutPerm le_rfl) (fixV (rImg (rhoC11 AutPerm le_rfl)
      (Subgroup.zpowers (koPerm 1)))) = (Subgroup.zpowers (koPerm 1)).subgroupOf M24g := by
  have hfix : fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))) = octWz := by
    rw [show rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1)) =
      imgCd (Subgroup.zpowers (koPerm 1)) from rfl]
    exact fixV_imgCd_zpowers_koOne
  rw [hfix]
  apply le_antisymm
  · intro γ hγ
    let γA : ↥AutPerm := ⟨γ.1, γ.2⟩
    have hγfix : ∀ x ∈ octWz, rhoC11 AutPerm le_rfl γA x = x :=
      (mem_cenM_iff (rhoC11 AutPerm le_rfl) octWz γA).1 (by
        change γ ∈ cenM (Γ := M24g) (rhoC11 AutPerm le_rfl) octWz
        exact hγ)
    have hγvz : ∀ x ∈ octVz, rhoC11 AutPerm le_rfl γA x = x :=
      fun x hx => hγfix x (octVz_le_octWz hx)
    have hγdGrp : (γA : S24) ∈ dGrp := mem_dGrp_of_fix_octVz γA hγvz
    obtain ⟨u, hu⟩ := mem_dGrp_iff.mp hγdGrp
    have hu_lt : (u : ℕ) < 2 := by
      apply dArr_triv_wz (u : ℕ) u.2
      intro m hm
      have hx : toW 11 m ∈ octWz := toW_mem_maskSub hm
      have hfixm := hγfix (toW 11 m) hx
      have hγeq : γA = (⟨dPerm u, dPerm_mem_M24g u⟩ : ↥AutPerm) := Subtype.ext hu.symm
      rw [hγeq, rhoC11_dPerm] at hfixm
      exact toW_inj (actC11_lt (dArr u) m) (combos_lt wz0Basis_lt m hm) hfixm
    rw [Subgroup.mem_subgroupOf]
    change (γA : S24) ∈ Subgroup.zpowers (koPerm 1)
    rw [← hu]
    have hu' : (u : ℕ) = 0 ∨ (u : ℕ) = 1 := by omega
    rcases hu' with h0 | h1
    · have hu0 : u = 0 := Fin.ext h0
      rw [hu0, dPerm_zero]
      exact Subgroup.one_mem _
    · have hu1 : u = 1 := Fin.ext h1
      rw [hu1, dPerm_one]
      exact Subgroup.mem_zpowers (koPerm 1)
  · intro γ hγ
    rw [Subgroup.mem_subgroupOf] at hγ
    let γA : ↥AutPerm := ⟨γ.1, γ.2⟩
    change γA ∈ cenM (Γ := AutPerm) (rhoC11 AutPerm le_rfl) octWz
    rw [mem_cenM_iff]
    intro x hx
    have hx' : x ∈ fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))) := by
      rwa [hfix]
    exact (mem_fixV.1 hx') (rhoC11 AutPerm le_rfl γA)
      (Subgroup.mem_map_of_mem (rhoC11 AutPerm le_rfl) (Subgroup.mem_subgroupOf.2 hγ))

theorem cenMS_octV5_inf_fixV :
    (cenM (Γ := M24g) (rhoC11 AutPerm le_rfl) (octV5 ⊓ fixV (rImg (rhoC11 AutPerm le_rfl)
      (Subgroup.zpowers (koPerm 1))))).map M24g.subtype = dGrp := by
  have hfix : fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))) = octWz := by
    rw [show rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1)) =
      imgCd (Subgroup.zpowers (koPerm 1)) from rfl]
    exact fixV_imgCd_zpowers_koOne
  have hW : octV5 ⊓ fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))) = octVz := by
    rw [hfix, octV5_inf_octWz]
  rw [hW, cenMS_octVz]

end CFSG.ASVolI.H16
