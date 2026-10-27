module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoF48Eqv

public noncomputable section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.H13.F48Gen
  CFSG.TitsF46 CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Ext

variable
  (h : Certificates.titsGeoFacts)
  (hc : Certificates.titsF48Facts)

theorem phiD_mem_B {x : Equiv.Perm (Fin 1755)} (hD : x ∈ titsD) (hH : x ∈ titsH)
    (hN : x ∈ titsN) :
    phiD ⟨x, hD⟩ ∈ stv titsSetting.ι titsSetting.ι.xv ⊓ stv titsSetting.ι titsSetting.ι.lv := by
  refine Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩
  · exact (smul_xv_iff' _ _).2 ((mem_range_φ1_iff _).2 (by rw [toPermD_phiD]; exact hH))
  · exact (smul_lv_iff' _ _).2 ((mem_range_φ2_iff _).2 (by rw [toPermD_phiD]; exact hN))

include h hc in
theorem fixed_point_eq_xv {v : titsSetting.ι.Γ} (hv : CosetGeom.vtype v = false)
    (hfix : ∀ b ∈ stv titsSetting.ι titsSetting.ι.xv ⊓ stv titsSetting.ι titsSetting.ι.lv,
      b • v = v) : v = titsSetting.ι.xv := by
  rcases v with w | w
  swap
  · simp [CosetGeom.vtype] at hv
  have hfixP : ∀ (x : Equiv.Perm (Fin 1755)), x ∈ titsH → x ∈ titsN →
      x (titsKappa h w) = titsKappa h w := by
    intro x hH hN
    have h1 := hfix (phiD ⟨x, titsH_le_titsD hH⟩) (phiD_mem_B (titsH_le_titsD hH) hH hN)
    have h2 := titsE_smul h ⟨x, titsH_le_titsD hH⟩ (Sum.inl w)
    rw [h1, titsE_kappa, dsmul_inl] at h2
    exact (Sum.inl_injective h2).symm
  obtain ⟨hfix0, -⟩ := hc
  apply (titsE h).injective
  rw [titsE_kappa, titsE_xv, hfix0 _ hfixP]

include h hc in
theorem center_eq_bot : Subgroup.center titsSetting.ι.G0 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hcomm : ∀ g : titsSetting.ι.G0, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  have hzx : z • titsSetting.ι.xv = titsSetting.ι.xv := by
    refine fixed_point_eq_xv h hc (by rw [CosetGeom.vtype_smul]; rfl) fun b hb => ?_
    have hb1 : b • titsSetting.ι.xv = titsSetting.ι.xv :=
      MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hb).1
    rw [smul_smul, hcomm b, mul_smul, hb1]
  have hz1 : z • ((1 : titsSetting.ι.G0) : Pt titsSetting.ι) =
      ((1 : titsSetting.ι.G0) : Pt titsSetting.ι) := by
    have h' := hzx
    change z • (Sum.inl ((1 : titsSetting.ι.G0) : Pt titsSetting.ι) : titsSetting.ι.Γ) =
      Sum.inl ((1 : titsSetting.ι.G0) : Pt titsSetting.ι) at h'
    rw [CosetGeom.smul_inl] at h'
    exact Sum.inl_injective h'
  have hzc : ((z : titsSetting.ι.G0) : Pt titsSetting.ι) =
      ((1 : titsSetting.ι.G0) : Pt titsSetting.ι) := by
    rw [← hz1, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  have htriv : MulAction.toPermHom titsSetting.ι.G0 (Pt titsSetting.ι) z = 1 := by
    refine Equiv.ext fun w => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← hcomm g, ← smul_eq_mul,
      ← MulAction.Quotient.smul_mk]
    change g • ((z : titsSetting.ι.G0) : Pt titsSetting.ι) = _
    rw [hzc, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  exact toPermD_injective h (htriv.trans (map_one _).symm)

include h hc in
theorem titsIsExtension : titsSetting.IsExtension titsSetting.ι.G0 := by
  have hN : titsSetting.N = ⊤ := rfl
  have hmap12 : titsSetting.N12.map titsSetting.N.subtype =
      stv titsSetting.ι titsSetting.ι.xv ⊓ stv titsSetting.ι titsSetting.ι.lv := by
    rw [LieSetting.N12, Subgroup.subgroupOf_map_subtype, hN, inf_top_eq]
  have hmap1 :
      titsSetting.N1.map titsSetting.N.subtype = stv titsSetting.ι titsSetting.ι.xv := by
    rw [LieSetting.N1, Subgroup.subgroupOf_map_subtype, hN, inf_top_eq]
  refine ⟨titsSetting.N.subtype, Subgroup.subtype_injective _, ?_, ?_, ?_⟩
  · rw [Subgroup.range_subtype]
    exact titsSetting.hN
  · rw [Subgroup.range_subtype, hN, Subgroup.coe_top, Subgroup.centralizer_univ]
    exact center_eq_bot h hc
  · intro g hg
    rw [hmap12] at hg
    rw [hmap1]
    have hgx : g • titsSetting.ι.xv = titsSetting.ι.xv := by
      refine fixed_point_eq_xv h hc (by rw [CosetGeom.vtype_smul]; rfl) fun b hb => ?_
      have h1 : g⁻¹ * b * g ∈ stv titsSetting.ι titsSetting.ι.xv ⊓
          stv titsSetting.ι titsSetting.ι.lv :=
        (Subgroup.mem_normalizer_iff''.1 hg b).1 hb
      have h2 : (g⁻¹ * b * g) • titsSetting.ι.xv = titsSetting.ι.xv :=
        MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 h1).1
      calc b • g • titsSetting.ι.xv = g • ((g⁻¹ * b * g) • titsSetting.ι.xv) := by
            simp only [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
        _ = g • titsSetting.ι.xv := by rw [h2]
    exact Subgroup.le_normalizer (MulAction.mem_stabilizer_iff.2 hgx)

end Ext

section Holds

variable
  (h : Certificates.titsGeoFacts)
  (hc : Certificates.titsF48Facts)

include h hc in
theorem titsF48_of_check (Y₀ : Type) [Group Y₀] [Finite Y₀] (β : titsSetting.α.Completion Y₀)
    (hβ : β.IsFaithful) (hs : β.IsSmall titsSetting.m) : titsSetting.F48Concl β := by
  obtain ⟨θ, hθ1, hθ2⟩ := titsF48_equiv_small h hc β hβ hs
  let eβ : β.G0 ≃* Y₀ := (MulEquiv.subgroupCongr β.gen).trans Subgroup.topEquiv
  let eι : titsSetting.ι.G0 ≃* titsSetting.Yb :=
    (MulEquiv.subgroupCongr titsSetting.ι.gen).trans Subgroup.topEquiv
  have hφ1 : ∀ p, (eβ.symm.trans (θ.trans eι)) (β.φ1 p) = titsSetting.ι.φ1 p := fun p => by
    have : eβ.symm (β.φ1 p) = f1 (c := β) p := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, hθ1]
    rfl
  have hφ2 : ∀ q, (eβ.symm.trans (θ.trans eι)) (β.φ2 q) = titsSetting.ι.φ2 q := fun q => by
    have : eβ.symm (β.φ2 q) = f2 (c := β) q := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, hθ2]
    rfl
  have heq : Amalgam.Completion.IsEquivalent β.toCompletion titsSetting.ι.toCompletion := by
    refine ⟨eβ.symm.trans (θ.trans eι), fun d x => ?_⟩
    cases d
    · exact hφ1 x
    · exact hφ2 x
    · have h1 := hφ1 (titsSetting.α.α1 (x : titsSetting.α.G12))
      have h2 := congrArg (eβ.symm.trans (θ.trans eι)) (β.comm1 (x : titsSetting.α.G12))
      exact (h2.symm.trans h1).trans (titsSetting.ι.comm1 (x : titsSetting.α.G12))
  let φY : Y₀ ≃* titsSetting.ι.G0 := eβ.symm.trans θ
  refine ⟨⟨titsSetting.ι.G0, inferInstance, mapEquivComp β φY, mapEquivComp_faithful hβ φY,
    mapEquivComp_equiv β φY, titsIsExtension h hc⟩, fun _ => ?_⟩
  rw [Amalgam.Completion.isQuasiEquivalent_iff_exists_act]
  exact ⟨1, by rw [Amalgam.Completion.act_one]; exact heq⟩

end Holds

end CFSG.Quasithin.TitsGeo
