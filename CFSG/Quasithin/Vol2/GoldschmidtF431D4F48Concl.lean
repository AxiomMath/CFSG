module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Equiv

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.H13.F48Gen
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Ext

variable (S : LieSetting.{0, 0})
  (hfix : ∀ v : S.ι.Γ, CosetGeom.vtype v = false →
    (∀ b ∈ stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv, b • v = v) → v = S.ι.xv)
  (hTι : Function.Injective (MulAction.toPermHom S.ι.G0 (Pt S.ι)))

include hfix hTι in
theorem f48_center_eq_bot : Subgroup.center S.ι.G0 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hcomm : ∀ g : S.ι.G0, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  have hzx : z • S.ι.xv = S.ι.xv := by
    refine hfix _ (by rw [CosetGeom.vtype_smul]; rfl) fun b hb => ?_
    have hb1 : b • S.ι.xv = S.ι.xv :=
      MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hb).1
    rw [smul_smul, hcomm b, mul_smul, hb1]
  have hz1 : z • ((1 : S.ι.G0) : Pt S.ι) = ((1 : S.ι.G0) : Pt S.ι) := by
    have h' := hzx
    change z • (Sum.inl ((1 : S.ι.G0) : Pt S.ι) : S.ι.Γ) = Sum.inl ((1 : S.ι.G0) : Pt S.ι) at h'
    rw [CosetGeom.smul_inl] at h'
    exact Sum.inl_injective h'
  have hzc : ((z : S.ι.G0) : Pt S.ι) = ((1 : S.ι.G0) : Pt S.ι) := by
    rw [← hz1, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  have htriv : MulAction.toPermHom S.ι.G0 (Pt S.ι) z = 1 := by
    refine Equiv.ext fun w => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← hcomm g, ← smul_eq_mul,
      ← MulAction.Quotient.smul_mk]
    change g • ((z : S.ι.G0) : Pt S.ι) = _
    rw [hzc, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  exact hTι (htriv.trans (map_one _).symm)

include hfix hTι in
theorem f48_isExtension (hN : S.N = ⊤) : S.IsExtension S.ι.G0 := by
  have hmap12 : S.N12.map S.N.subtype = stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv := by
    rw [LieSetting.N12, Subgroup.subgroupOf_map_subtype, hN, inf_top_eq]
  have hmap1 : S.N1.map S.N.subtype = stv S.ι S.ι.xv := by
    rw [LieSetting.N1, Subgroup.subgroupOf_map_subtype, hN, inf_top_eq]
  refine ⟨S.N.subtype, Subgroup.subtype_injective _, ?_, ?_, ?_⟩
  · rw [Subgroup.range_subtype]
    exact S.hN
  · rw [Subgroup.range_subtype, hN, Subgroup.coe_top, Subgroup.centralizer_univ]
    exact f48_center_eq_bot S hfix hTι
  · intro g hg
    rw [hmap12] at hg
    rw [hmap1]
    have hgx : g • S.ι.xv = S.ι.xv := by
      refine hfix _ (by rw [CosetGeom.vtype_smul]; rfl) fun b hb => ?_
      have h1 : g⁻¹ * b * g ∈ stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv :=
        (Subgroup.mem_normalizer_iff''.1 hg b).1 hb
      have h2 : (g⁻¹ * b * g) • S.ι.xv = S.ι.xv :=
        MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 h1).1
      calc b • g • S.ι.xv = g • ((g⁻¹ * b * g) • S.ι.xv) := by
            simp only [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
        _ = g • S.ι.xv := by rw [h2]
    exact Subgroup.le_normalizer (MulAction.mem_stabilizer_iff.2 hgx)

end Ext

section Gen

variable (S : LieSetting.{0, 0})
  (hfix : ∀ v : S.ι.Γ, CosetGeom.vtype v = false →
    (∀ b ∈ S.N ⊓ (stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv), b • v = v) → v = S.ι.xv)
  (hNtr : ∀ v : S.ι.Γ, CosetGeom.vtype v = false → ∃ g ∈ S.N, g • S.ι.xv = v)
  (hTι : Function.Injective (MulAction.toPermHom S.ι.G0 (Pt S.ι)))

include hfix hNtr hTι in
theorem f48_isExtension_gen : S.IsExtension S.ι.G0 := by
  have hmap12 : S.N12.map S.N.subtype = stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv ⊓ S.N := by
    rw [LieSetting.N12, Subgroup.subgroupOf_map_subtype]
  have hmap1 : S.N1.map S.N.subtype = stv S.ι S.ι.xv ⊓ S.N := by
    rw [LieSetting.N1, Subgroup.subgroupOf_map_subtype]
  refine ⟨S.N.subtype, Subgroup.subtype_injective _, ?_, ?_, ?_⟩
  · rw [Subgroup.range_subtype]
    exact S.hN
  · rw [Subgroup.range_subtype]
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    have hc : ∀ g ∈ S.N, g * z = z * g := fun g hg => Subgroup.mem_centralizer_iff.1 hz g hg
    have hzx : z • S.ι.xv = S.ι.xv := by
      refine hfix _ (by rw [CosetGeom.vtype_smul]; rfl) fun b hb => ?_
      have hbN : b ∈ S.N := (Subgroup.mem_inf.1 hb).1
      have hb1 : b • S.ι.xv = S.ι.xv :=
        MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).2).1
      rw [smul_smul, hc b hbN, mul_smul, hb1]
    have htriv : ∀ v : S.ι.Γ, CosetGeom.vtype v = false → z • v = v := by
      intro v hv
      obtain ⟨g, hgN, rfl⟩ := hNtr v hv
      rw [smul_smul, ← hc g hgN, mul_smul, hzx]
    have hz1 : MulAction.toPermHom S.ι.G0 (Pt S.ι) z = 1 := by
      refine Equiv.ext fun w => ?_
      have := htriv (Sum.inl w) (by simp [CosetGeom.vtype])
      rw [CosetGeom.smul_inl] at this
      exact Sum.inl_injective this
    exact hTι (hz1.trans (map_one _).symm)
  · intro g hg
    rw [hmap12] at hg
    rw [hmap1]
    have hgx : g • S.ι.xv = S.ι.xv := by
      refine hfix _ (by rw [CosetGeom.vtype_smul]; rfl) fun b hb => ?_
      have hb' : b ∈ stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv ⊓ S.N :=
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hb).2, (Subgroup.mem_inf.1 hb).1⟩
      have h1 := (Subgroup.mem_normalizer_iff''.1 hg b).1 hb'
      have h2 : (g⁻¹ * b * g) • S.ι.xv = S.ι.xv :=
        MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 h1).1).1
      calc b • g • S.ι.xv = g • ((g⁻¹ * b * g) • S.ι.xv) := by
            simp only [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
        _ = g • S.ι.xv := by rw [h2]
    have hgs : g ∈ stv S.ι S.ι.xv := MulAction.mem_stabilizer_iff.2 hgx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 hh
      exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgs hh1) (inv_mem hgs), S.hN.conj_mem h hh2 g⟩
    · intro hh
      obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 hh
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · simpa [mul_assoc] using mul_mem (mul_mem (inv_mem hgs) hh1) hgs
      · simpa [mul_assoc] using S.hN.conj_mem _ hh2 g⁻¹

end Gen

section Concl

variable (S : LieSetting.{0, 0}) {k : ℕ} (hm : S.m = k + 2) (M : TitsModel S.ι k)
  (hpoly : IsGenPolygon S.ι.graph S.m) {n : S.α.G1} {q : S.α.G2} {Mord : ℕ}
  (hcard : Nat.card S.Yb ∣ Mord) (hrig : PtRigid S n q Mord)
  (hTι : Function.Injective (MulAction.toPermHom S.ι.G0 (Pt S.ι)))
  (hExt : S.IsExtension S.ι.G0)

include hm M hpoly hcard hrig hTι hExt in
theorem f48Concl_of_ext (Y₀ : Type) [Group Y₀] [Finite Y₀] (β : S.α.Completion Y₀)
    (hβ : β.IsFaithful) (hs : β.IsSmall S.m) : S.F48Concl β := by
  obtain ⟨θ, hθ1, hθ2⟩ := f48_equiv_small S hm M hpoly hcard hrig hTι β hβ hs
  let eβ : β.G0 ≃* Y₀ := (MulEquiv.subgroupCongr β.gen).trans Subgroup.topEquiv
  let eι : S.ι.G0 ≃* S.Yb := (MulEquiv.subgroupCongr S.ι.gen).trans Subgroup.topEquiv
  have hφ1 : ∀ p, (eβ.symm.trans (θ.trans eι)) (β.φ1 p) = S.ι.φ1 p := fun p => by
    have : eβ.symm (β.φ1 p) = f1 (c := β) p := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, hθ1]
    rfl
  have hφ2 : ∀ q, (eβ.symm.trans (θ.trans eι)) (β.φ2 q) = S.ι.φ2 q := fun q => by
    have : eβ.symm (β.φ2 q) = f2 (c := β) q := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, hθ2]
    rfl
  have heq : Amalgam.Completion.IsEquivalent β.toCompletion S.ι.toCompletion := by
    refine ⟨eβ.symm.trans (θ.trans eι), fun d x => ?_⟩
    cases d
    · exact hφ1 x
    · exact hφ2 x
    · have h1 := hφ1 (S.α.α1 (x : S.α.G12))
      have h2 := congrArg (eβ.symm.trans (θ.trans eι)) (β.comm1 (x : S.α.G12))
      exact (h2.symm.trans h1).trans (S.ι.comm1 (x : S.α.G12))
  let φY : Y₀ ≃* S.ι.G0 := eβ.symm.trans θ
  refine ⟨⟨S.ι.G0, inferInstance, mapEquivComp β φY, mapEquivComp_faithful hβ φY,
    mapEquivComp_equiv β φY, hExt⟩, fun _ => ?_⟩
  rw [Amalgam.Completion.isQuasiEquivalent_iff_exists_act]
  exact ⟨1, by rw [Amalgam.Completion.act_one]; exact heq⟩

end Concl

section Top

variable (S : LieSetting.{0, 0}) {k : ℕ} (hm : S.m = k + 2) (M : TitsModel S.ι k)
  (hpoly : IsGenPolygon S.ι.graph S.m) {n : S.α.G1} {q : S.α.G2} {Mord : ℕ}
  (hcard : Nat.card S.Yb ∣ Mord) (hrig : PtRigid S n q Mord)
  (hTι : Function.Injective (MulAction.toPermHom S.ι.G0 (Pt S.ι)))
  (hfix : ∀ v : S.ι.Γ, CosetGeom.vtype v = false →
    (∀ b ∈ stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv, b • v = v) → v = S.ι.xv)
  (hN : S.N = ⊤)

include hm M hpoly hcard hrig hTι hfix hN in
theorem f48Concl_of_rigid (Y₀ : Type) [Group Y₀] [Finite Y₀] (β : S.α.Completion Y₀)
    (hβ : β.IsFaithful) (hs : β.IsSmall S.m) : S.F48Concl β :=
  f48Concl_of_ext S hm M hpoly hcard hrig hTι (f48_isExtension S hfix hTι hN) Y₀ β hβ hs

end Top

end CFSG.Quasithin.D4Hex
