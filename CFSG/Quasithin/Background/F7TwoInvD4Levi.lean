module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviModules
public import CFSG.Quasithin.Background.F7TwoInvBridge
public import CFSG.Quasithin.Background.F7TwoInvD4Sl2

public section

namespace CFSG.Quasithin.F7Two

open CFSG.LocalAnalysis.EvenBN.TrialityD4 CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem slU₁_eq (b : d.Γ) : d.slU₁ b = utriElt b :=
  sl2_ext (by simp [TrialityD4Data.slU₁, utriElt_apply_00]) (by simp [TrialityD4Data.slU₁,
    utriElt_apply_01]) (by simp [TrialityD4Data.slU₁, utriElt_apply_10]) (by
    simp [TrialityD4Data.slU₁, utriElt_apply_11])

theorem slX₂_eq (a : d.Γ₀) : d.slX₂ a = ltriElt a :=
  sl2_ext (by simp [TrialityD4Data.slX₂, ltriElt_apply_00]) (by simp [TrialityD4Data.slX₂,
    ltriElt_apply_01]) (by simp [TrialityD4Data.slX₂, ltriElt_apply_10]) (by
    simp [TrialityD4Data.slX₂, ltriElt_apply_11])

theorem leviShortEquiv_x₁ (b : d.Γ) :
    d.leviShortEquiv ⟨d.x₁ b, d.x₁_mem_leviShort b⟩ = utriElt b := by
  rw [← slU₁_eq]
  change d.leviShortRep _ = _
  exact eq_of_mob_eq fun z => by rw [← d.leviShortRep_spec, d.leviShortAct_x₁]

theorem leviShortEquiv_u : ∃ (r : d.Γ) (hr : r ≠ 0),
    d.leviShortEquiv ⟨d.u, d.u_mem_leviShort⟩ = d.slW r hr := by
  obtain ⟨r, hr, h⟩ := d.exists_leviShortAct_u
  refine ⟨r, hr, ?_⟩
  change d.leviShortRep _ = _
  exact eq_of_mob_eq fun z => by rw [← d.leviShortRep_spec, h]

theorem leviLongEquiv_x₂ (a : d.Γ₀) :
    d.leviLongEquiv ⟨d.x₂ a, d.x₂_mem_leviLong a⟩ = ltriElt a := by
  rw [← slX₂_eq, d.leviLongEquiv_apply]
  exact d.sl_eq_of_yv fun w => by rw [← d.leviLongRep_spec]; exact d.x₂_conj_yv a w

theorem leviLongEquiv_v : d.leviLongEquiv ⟨d.v, d.v_mem_leviLong⟩ = d.slV := by
  rw [d.leviLongEquiv_apply]
  exact d.sl_eq_of_yv fun w => by rw [← d.leviLongRep_spec]; exact d.v_conj_yv w

theorem u_mem_U₁_sup_conj :
    d.u ∈ d.U₁ ⊔ d.U₁.map (MulAut.conj d.u).toMonoidHom := by
  obtain ⟨r, hr, hu⟩ := leviShortEquiv_u d
  have hW00 : ((d.slW r hr : SL(2, d.Γ)) : Matrix (Fin 2) (Fin 2) d.Γ) 0 0 = 0 := by
    simp [TrialityD4Data.slW]
  have hW11 : ((d.slW r hr : SL(2, d.Γ)) : Matrix (Fin 2) (Fin 2) d.Γ) 1 1 = 0 := by
    simp [TrialityD4Data.slW]
  set T : Subgroup d.leviShort :=
    (d.U₁ ⊔ d.U₁.map (MulAut.conj d.u).toMonoidHom).subgroupOf d.leviShort with hT
  have hle : utri d.Γ ⊔ (utri d.Γ).map (MulAut.conj (d.slW r hr)).toMonoidHom ≤
      T.map d.leviShortEquiv.toMonoidHom := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨b, rfl⟩ := mem_utri_iff.1 hg
      exact ⟨⟨d.x₁ b, d.x₁_mem_leviShort b⟩,
        Subgroup.mem_sup_left ⟨b, rfl⟩, leviShortEquiv_x₁ d b⟩
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨b, rfl⟩ := mem_utri_iff.1 hg
      refine ⟨⟨d.u * d.x₁ b * d.u⁻¹, mul_mem (mul_mem d.u_mem_leviShort (d.x₁_mem_leviShort b))
        (inv_mem d.u_mem_leviShort)⟩, Subgroup.mem_sup_right ⟨d.x₁ b, ⟨b, rfl⟩, rfl⟩, ?_⟩
      have e : (⟨d.u * d.x₁ b * d.u⁻¹, mul_mem (mul_mem d.u_mem_leviShort
          (d.x₁_mem_leviShort b)) (inv_mem d.u_mem_leviShort)⟩ : d.leviShort) =
          ⟨d.u, d.u_mem_leviShort⟩ * ⟨d.x₁ b, d.x₁_mem_leviShort b⟩ *
            ⟨d.u, d.u_mem_leviShort⟩⁻¹ := rfl
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [e, map_mul, map_mul, map_inv, hu, leviShortEquiv_x₁ d]
  have htop := utri_sup_conj_eq_top hW00 hW11
  have hmem : (⟨d.u, d.u_mem_leviShort⟩ : d.leviShort) ∈ T := by
    obtain ⟨g', hg', e⟩ : d.leviShortEquiv ⟨d.u, d.u_mem_leviShort⟩ ∈
        T.map d.leviShortEquiv.toMonoidHom := hle (htop ▸ Subgroup.mem_top _)
    exact d.leviShortEquiv.injective e ▸ hg'
  exact Subgroup.mem_subgroupOf.1 hmem

theorem v_mem_U₂_sup_conj :
    d.v ∈ d.U₂ ⊔ d.U₂.map (MulAut.conj d.v).toMonoidHom := by
  have hW00 : ((d.slV : SL(2, d.Γ₀)) : Matrix (Fin 2) (Fin 2) d.Γ₀) 0 0 = 0 := by
    simp [TrialityD4Data.slV]
  have hW11 : ((d.slV : SL(2, d.Γ₀)) : Matrix (Fin 2) (Fin 2) d.Γ₀) 1 1 = 0 := by
    simp [TrialityD4Data.slV]
  set T : Subgroup d.leviLong :=
    (d.U₂ ⊔ d.U₂.map (MulAut.conj d.v).toMonoidHom).subgroupOf d.leviLong with hT
  have hle : ltri d.Γ₀ ⊔ (ltri d.Γ₀).map (MulAut.conj d.slV).toMonoidHom ≤
      T.map d.leviLongEquiv.toMonoidHom := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨b, rfl⟩ := mem_ltri_iff.1 hg
      exact ⟨⟨d.x₂ b, d.x₂_mem_leviLong b⟩,
        Subgroup.mem_sup_left ⟨b, rfl⟩, leviLongEquiv_x₂ d b⟩
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨b, rfl⟩ := mem_ltri_iff.1 hg
      refine ⟨⟨d.v * d.x₂ b * d.v⁻¹, mul_mem (mul_mem d.v_mem_leviLong (d.x₂_mem_leviLong b))
        (inv_mem d.v_mem_leviLong)⟩, Subgroup.mem_sup_right ⟨d.x₂ b, ⟨b, rfl⟩, rfl⟩, ?_⟩
      have e : (⟨d.v * d.x₂ b * d.v⁻¹, mul_mem (mul_mem d.v_mem_leviLong
          (d.x₂_mem_leviLong b)) (inv_mem d.v_mem_leviLong)⟩ : d.leviLong) =
          ⟨d.v, d.v_mem_leviLong⟩ * ⟨d.x₂ b, d.x₂_mem_leviLong b⟩ *
            ⟨d.v, d.v_mem_leviLong⟩⁻¹ := rfl
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [e, map_mul, map_mul, map_inv, leviLongEquiv_v d, leviLongEquiv_x₂ d]
  have htop := ltri_sup_conj_eq_top hW00 hW11
  have hmem : (⟨d.v, d.v_mem_leviLong⟩ : d.leviLong) ∈ T := by
    obtain ⟨g', hg', e⟩ : d.leviLongEquiv ⟨d.v, d.v_mem_leviLong⟩ ∈
        T.map d.leviLongEquiv.toMonoidHom := hle (htop ▸ Subgroup.mem_top _)
    exact d.leviLongEquiv.injective e ▸ hg'
  exact Subgroup.mem_subgroupOf.1 hmem

theorem not_isPGroup_x₁_mul_conj :
    ¬ IsPGroup 2 ↥(Subgroup.zpowers (d.x₁ 1 * (d.u * d.x₁ 1 * d.u⁻¹))) := by
  obtain ⟨r, hr, hu⟩ := leviShortEquiv_u d
  have hW00 : ((d.slW r hr : SL(2, d.Γ)) : Matrix (Fin 2) (Fin 2) d.Γ) 0 0 = 0 := by
    simp [TrialityD4Data.slW]
  have hW11 : ((d.slW r hr : SL(2, d.Γ)) : Matrix (Fin 2) (Fin 2) d.Γ) 1 1 = 0 := by
    simp [TrialityD4Data.slW]
  set g : d.leviShort := ⟨d.x₁ 1, d.x₁_mem_leviShort 1⟩ *
    (⟨d.u, d.u_mem_leviShort⟩ * ⟨d.x₁ 1, d.x₁_mem_leviShort 1⟩ * ⟨d.u, d.u_mem_leviShort⟩⁻¹)
    with hg
  have h1 : ¬ IsPGroup 2 ↥(Subgroup.zpowers (d.leviShortEquiv g)) := by
    rw [hg, map_mul, map_mul, map_mul, map_inv, hu, leviShortEquiv_x₁ d]
    exact not_isPGroup_utri_mul_conj hW00 hW11
  exact fun h => h1 ((isPGroup_zpowers_map_iff d.leviShortEquiv.toMonoidHom
    d.leviShortEquiv.injective g).2 ((isPGroup_zpowers_map_iff d.leviShort.subtype
    d.leviShort.subtype_injective g).1 h))

theorem not_isPGroup_x₂_mul_conj :
    ¬ IsPGroup 2 ↥(Subgroup.zpowers (d.x₂ 1 * (d.v * d.x₂ 1 * d.v⁻¹))) := by
  have hW00 : ((d.slV : SL(2, d.Γ₀)) : Matrix (Fin 2) (Fin 2) d.Γ₀) 0 0 = 0 := by
    simp [TrialityD4Data.slV]
  have hW11 : ((d.slV : SL(2, d.Γ₀)) : Matrix (Fin 2) (Fin 2) d.Γ₀) 1 1 = 0 := by
    simp [TrialityD4Data.slV]
  set g : d.leviLong := ⟨d.x₂ 1, d.x₂_mem_leviLong 1⟩ *
    (⟨d.v, d.v_mem_leviLong⟩ * ⟨d.x₂ 1, d.x₂_mem_leviLong 1⟩ * ⟨d.v, d.v_mem_leviLong⟩⁻¹)
    with hg
  have h1 : ¬ IsPGroup 2 ↥(Subgroup.zpowers (d.leviLongEquiv g)) := by
    rw [hg, map_mul, map_mul, map_mul, map_inv, leviLongEquiv_v d, leviLongEquiv_x₂ d]
    exact not_isPGroup_ltri_mul_conj hW00 hW11
  exact fun h => h1 ((isPGroup_zpowers_map_iff d.leviLongEquiv.toMonoidHom
    d.leviLongEquiv.injective g).2 ((isPGroup_zpowers_map_iff d.leviLong.subtype
    d.leviLong.subtype_injective g).1 h))

end CFSG.Quasithin.F7Two
