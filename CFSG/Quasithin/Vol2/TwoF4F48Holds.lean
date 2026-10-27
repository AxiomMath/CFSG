module

public import CFSG.Quasithin.Vol2.TwoF4F48Eqv

public section

namespace CFSG.Quasithin.H13.TwoF4F48

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.Quasithin.RuType
  CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.H13.F48Gen CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.TwoF4F48 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

section Ext


theorem phiA_mem_B {x : Equiv.Perm (Fin 1755)} (hA : x ∈ TA) (hH : x ∈ twoF4H)
    (hN : x ∈ twoF4N) :
    phiA ⟨x, hA⟩ ∈ stv twoF4Setting.ι twoF4Setting.ι.xv ⊓
      stv twoF4Setting.ι twoF4Setting.ι.lv := by
  refine Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩
  · exact (smul_xv_iff' _ _).2 ((mem_range_φ1_iff _).2 (by rw [toPerm_phiA]; exact hH))
  · exact (smul_lv_iff' _ _).2 ((mem_range_φ2_iff _).2 (by rw [toPerm_phiA]; exact hN))

theorem fixed_point_eq_xv {v : twoF4Setting.ι.Γ} (hv : CosetGeom.vtype v = false)
    (hfix : ∀ b ∈ stv twoF4Setting.ι twoF4Setting.ι.xv ⊓ stv twoF4Setting.ι twoF4Setting.ι.lv,
      b • v = v) :
    v = twoF4Setting.ι.xv := by
  rcases v with w | w
  swap
  · simp [CosetGeom.vtype] at hv
  have hfixP : ∀ (x : Equiv.Perm (Fin 1755)) (hA : x ∈ TA), x ∈ twoF4H → x ∈ twoF4N →
      x (twoF4Kappa w) = twoF4Kappa w := by
    intro x hA hH hN
    have h1 := hfix _ (phiA_mem_B hA hH hN)
    have h2 := twoF4E_smul ⟨x, hA⟩ (Sum.inl w)
    rw [h1, twoF4E_kappa, smul_inl] at h2
    exact (Sum.inl_injective h2).symm
  have hk0 : twoF4Kappa w = 0 := by
    by_contra hne
    obtain ⟨b, hbA, ⟨hb0, hbl⟩, hbp⟩ := fix_spec (twoF4Kappa w) hne
    exact hbp (hfixP b hbA ((J47.mem_twoF4H_iff hbA).2 hb0) ((J47.mem_twoF4N_iff hbA).2 hbl))
  apply twoF4E.injective
  rw [twoF4E_kappa, twoF4E_xv, hk0]

theorem center_eq_bot : Subgroup.center twoF4Setting.ι.G0 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hcomm : ∀ g : twoF4Setting.ι.G0, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  have hzx : z • twoF4Setting.ι.xv = twoF4Setting.ι.xv := by
    refine fixed_point_eq_xv (by rw [CosetGeom.vtype_smul]; rfl) fun b hb => ?_
    have hb1 : b • twoF4Setting.ι.xv = twoF4Setting.ι.xv :=
      MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hb).1
    rw [smul_smul, hcomm b, mul_smul, hb1]
  have hz1 : z • ((1 : twoF4Setting.ι.G0) : Pt twoF4Setting.ι) =
      ((1 : twoF4Setting.ι.G0) : Pt twoF4Setting.ι) := by
    have h := hzx
    change z • (Sum.inl ((1 : twoF4Setting.ι.G0) : Pt twoF4Setting.ι) : twoF4Setting.ι.Γ) =
      Sum.inl ((1 : twoF4Setting.ι.G0) : Pt twoF4Setting.ι) at h
    rw [CosetGeom.smul_inl] at h
    exact Sum.inl_injective h
  have hzc : ((z : twoF4Setting.ι.G0) : Pt twoF4Setting.ι) =
      ((1 : twoF4Setting.ι.G0) : Pt twoF4Setting.ι) := by
    rw [← hz1, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  have htriv : MulAction.toPermHom twoF4Setting.ι.G0 (Pt twoF4Setting.ι) z = 1 := by
    refine Equiv.ext fun w => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← hcomm g, ← smul_eq_mul,
      ← MulAction.Quotient.smul_mk]
    change g • ((z : twoF4Setting.ι.G0) : Pt twoF4Setting.ι) = _
    rw [hzc, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  exact toPerm_injective (htriv.trans (map_one _).symm)

theorem twoF4_isExtension : twoF4Setting.IsExtension twoF4Setting.ι.G0 := by
  have hN : twoF4Setting.N = ⊤ := rfl
  have hmap12 : twoF4Setting.N12.map twoF4Setting.N.subtype =
      stv twoF4Setting.ι twoF4Setting.ι.xv ⊓ stv twoF4Setting.ι twoF4Setting.ι.lv := by
    rw [LieSetting.N12, Subgroup.subgroupOf_map_subtype, hN, inf_top_eq]
  have hmap1 :
      twoF4Setting.N1.map twoF4Setting.N.subtype = stv twoF4Setting.ι twoF4Setting.ι.xv := by
    rw [LieSetting.N1, Subgroup.subgroupOf_map_subtype, hN, inf_top_eq]
  refine ⟨twoF4Setting.N.subtype, Subgroup.subtype_injective _, ?_, ?_, ?_⟩
  · rw [Subgroup.range_subtype]
    exact twoF4Setting.hN
  · rw [Subgroup.range_subtype, hN, Subgroup.coe_top, Subgroup.centralizer_univ]
    exact center_eq_bot
  · intro g hg
    rw [hmap12] at hg
    rw [hmap1]
    have hgx : g • twoF4Setting.ι.xv = twoF4Setting.ι.xv := by
      refine fixed_point_eq_xv (by rw [CosetGeom.vtype_smul]; rfl) fun b hb => ?_
      have h1 : g⁻¹ * b * g ∈ stv twoF4Setting.ι twoF4Setting.ι.xv ⊓
          stv twoF4Setting.ι twoF4Setting.ι.lv :=
        (Subgroup.mem_normalizer_iff''.1 hg b).1 hb
      have h2 : (g⁻¹ * b * g) • twoF4Setting.ι.xv = twoF4Setting.ι.xv :=
        MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 h1).1
      calc b • g • twoF4Setting.ι.xv = g • ((g⁻¹ * b * g) • twoF4Setting.ι.xv) := by
            simp only [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
        _ = g • twoF4Setting.ι.xv := by rw [h2]
    exact Subgroup.le_normalizer (MulAction.mem_stabilizer_iff.2 hgx)

end Ext

section Holds


theorem f48TwoF4_of_check : RuType.F48TwoF4 := by
  intro Y₀ _ _ β hβ hs
  obtain ⟨θ, hθ1, hθ2⟩ := twoF4_equiv_small β hβ hs
  let eβ : β.G0 ≃* Y₀ := (MulEquiv.subgroupCongr β.gen).trans Subgroup.topEquiv
  let eι : twoF4Setting.ι.G0 ≃* twoF4Setting.Yb :=
    (MulEquiv.subgroupCongr twoF4Setting.ι.gen).trans Subgroup.topEquiv
  have hφ1 : ∀ p, (eβ.symm.trans (θ.trans eι)) (β.φ1 p) = twoF4Setting.ι.φ1 p := fun p => by
    have : eβ.symm (β.φ1 p) = f1 (c := β) p := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, hθ1]
    rfl
  have hφ2 : ∀ q, (eβ.symm.trans (θ.trans eι)) (β.φ2 q) = twoF4Setting.ι.φ2 q := fun q => by
    have : eβ.symm (β.φ2 q) = f2 (c := β) q := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, hθ2]
    rfl
  have heq : Amalgam.Completion.IsEquivalent β.toCompletion twoF4Setting.ι.toCompletion := by
    refine ⟨eβ.symm.trans (θ.trans eι), fun d x => ?_⟩
    cases d
    · exact hφ1 x
    · exact hφ2 x
    · have h1 := hφ1 (twoF4Setting.α.α1 (x : twoF4Setting.α.G12))
      have h2 := congrArg (eβ.symm.trans (θ.trans eι)) (β.comm1 (x : twoF4Setting.α.G12))
      exact (h2.symm.trans h1).trans (twoF4Setting.ι.comm1 (x : twoF4Setting.α.G12))
  let φY : Y₀ ≃* twoF4Setting.ι.G0 := eβ.symm.trans θ
  refine ⟨⟨twoF4Setting.ι.G0, inferInstance, mapEquivComp β φY, mapEquivComp_faithful hβ φY,
    mapEquivComp_equiv β φY, twoF4_isExtension⟩, fun _ => ?_⟩
  rw [Amalgam.Completion.isQuasiEquivalent_iff_exists_act]
  exact ⟨1, by rw [Amalgam.Completion.act_one]; exact heq⟩

end Holds

end CFSG.Quasithin.H13.TwoF4F48
