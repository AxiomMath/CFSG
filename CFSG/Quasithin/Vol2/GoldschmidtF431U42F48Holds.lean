module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Eqv
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Def

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Ext


@[expose] noncomputable def u42NuY : ↥u42Setting.N →* Y :=
  eG.symm.toMonoidHom.comp u42Setting.N.subtype

theorem u42NuY_surjective : Function.Surjective u42NuY := fun y =>
  ⟨⟨eG y, by rw [N_eq_top]; trivial⟩, by simp [u42NuY]⟩

theorem u42_map_N1_nuY : u42Setting.N1.map u42NuY = P1 := by
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn' : (n : u42Setting.ι.G0) ∈ stv u42Setting.ι u42Setting.ι.xv := hn
    refine (mem_stv_xv_iff (eG.symm n)).1 ?_
    rw [show toG0 (eG.symm n) = n from eG.apply_symm_apply n]
    exact hn'
  · intro hy
    refine ⟨⟨eG y, by rw [N_eq_top]; trivial⟩, ?_, by simp [u42NuY]⟩
    show eG y ∈ stv u42Setting.ι u42Setting.ι.xv
    exact (mem_stv_xv_iff y).2 hy

theorem u42_map_N12_nuY : u42Setting.N12.map u42NuY = B0 := by
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn' : (n : u42Setting.ι.G0) ∈ stv u42Setting.ι u42Setting.ι.xv ⊓
        stv u42Setting.ι u42Setting.ι.lv := hn
    rw [Subgroup.mem_inf] at hn'
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · refine (mem_stv_xv_iff (eG.symm n)).1 ?_
      rw [show toG0 (eG.symm n) = n from eG.apply_symm_apply n]
      exact hn'.1
    · refine (mem_stv_lv_iff (eG.symm n)).1 ?_
      rw [show toG0 (eG.symm n) = n from eG.apply_symm_apply n]
      exact hn'.2
  · intro hy
    rw [B0, Subgroup.mem_inf] at hy
    refine ⟨⟨eG y, by rw [N_eq_top]; trivial⟩, ?_, by simp [u42NuY]⟩
    show eG y ∈ stv u42Setting.ι u42Setting.ι.xv ⊓ stv u42Setting.ι u42Setting.ι.lv
    exact Subgroup.mem_inf.2 ⟨(mem_stv_xv_iff y).2 hy.1, (mem_stv_lv_iff y).2 hy.2⟩

theorem u42_isExtension : u42Setting.IsExtension Y := by
  have hrange : u42NuY.range = ⊤ := MonoidHom.range_eq_top.2 u42NuY_surjective
  refine ⟨u42NuY, eG.symm.injective.comp Subtype.val_injective, ?_, ?_, ?_⟩
  · rw [hrange]
    exact Subgroup.normal_top
  · rw [hrange, Subgroup.coe_top, Subgroup.centralizer_univ, center_eq_bot]
  · intro g hg
    rw [u42_map_N12_nuY, normalizer_B0] at hg
    rw [u42_map_N1_nuY, normalizer_P1]
    exact B0_le_P1 hg

end Ext

section Holds

theorem u42F48_holds :
    U42F48 := by
  intro Y₀ _ _ β hβ hs
  obtain ⟨θ, hθ1, hθ2⟩ := u42_equiv_small β hβ hs
  let eβ : β.G0 ≃* Y₀ := (MulEquiv.subgroupCongr β.gen).trans Subgroup.topEquiv
  let eι : u42Setting.ι.G0 ≃* u42Setting.Yb :=
    (MulEquiv.subgroupCongr u42Setting.ι.gen).trans Subgroup.topEquiv
  have hφ1 : ∀ p, (eβ.symm.trans (θ.trans eι)) (β.φ1 p) = u42Setting.ι.φ1 p := fun p => by
    have : eβ.symm (β.φ1 p) = f1 (c := β) p := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, hθ1]
    rfl
  have hφ2 : ∀ q, (eβ.symm.trans (θ.trans eι)) (β.φ2 q) = u42Setting.ι.φ2 q := fun q => by
    have : eβ.symm (β.φ2 q) = f2 (c := β) q := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, hθ2]
    rfl
  have heq : Amalgam.Completion.IsEquivalent β.toCompletion u42Setting.ι.toCompletion := by
    refine ⟨eβ.symm.trans (θ.trans eι), fun d x => ?_⟩
    cases d
    · exact hφ1 x
    · exact hφ2 x
    · have h1 := hφ1 (u42Setting.α.α1 (x : u42Setting.α.G12))
      have h2 := congrArg (eβ.symm.trans (θ.trans eι)) (β.comm1 (x : u42Setting.α.G12))
      exact (h2.symm.trans h1).trans (u42Setting.ι.comm1 (x : u42Setting.α.G12))
  let φY : Y₀ ≃* Y := eβ.symm.trans (θ.trans eG.symm)
  refine ⟨⟨Y, inferInstance, f48MapEquivComp β φY, f48MapEquivComp_faithful hβ φY,
    f48MapEquivComp_equiv β φY, u42_isExtension⟩, fun _ => ?_⟩
  rw [Amalgam.Completion.isQuasiEquivalent_iff_exists_act]
  exact ⟨1, by rw [Amalgam.Completion.act_one]; exact heq⟩

end Holds

end CFSG.Quasithin.H13.F431.U42
