module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.MathieuExtPlane
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13

open CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane CFSG.Fischer
  CFSG.EvenSmallLie.UnitarySix.MathieuExt
open scoped MatrixGroups Matrix

@[expose] noncomputable def planePerm : GammaL3 →* Equiv.Perm (Fin 21) :=
  ptEquiv.symm.permCongrHom.toMonoidHom.comp rhoGL

theorem planePerm_apply (g : GammaL3) (i : Fin 21) :
    planePerm g i = ptEquiv.symm (rhoGL g (ptEquiv i)) := rfl

@[expose] def semΓ (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) : GammaL3 :=
  ⟨slinPerm A σ, slinPerm_mem A σ⟩

theorem semΓ_apply (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) (v : Vec3) :
    ((semΓ A σ : GammaL3) : Equiv.Perm Vec3) v = slin A σ v := rfl

theorem slin_ne_zero (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) {v : Vec3} (hv : v ≠ 0) :
    slin A σ v ≠ 0 := by
  intro h
  apply hv
  have h0 : slin A σ 0 = 0 := slin_zero A σ
  exact (slinPerm A σ).injective (h.trans h0.symm)

theorem imgSub_span_semΓ (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) (v : Vec3) :
    imgSub (semΓ A σ) (Submodule.span F4 {v}) = Submodule.span F4 {slin A σ v} := by
  ext w
  rw [mem_imgSub, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨σ c, by rw [semΓ_apply, slin_smul]⟩
  · rintro ⟨a, rfl⟩
    refine ⟨σ.symm a • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v), ?_⟩
    rw [semΓ_apply, slin_smul, RingEquiv.apply_symm_apply]

theorem planePerm_semΓ (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) (i : Fin 21) :
    planePerm (semΓ A σ) i = normIdx (slin A σ (Ω i)) := by
  rw [planePerm_apply, Equiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [coe_rhoGL_apply, coe_ptEquiv, coe_ptEquiv, imgSub_span_semΓ]
  obtain ⟨c, hc, hv⟩ := exists_smul_Ω_normIdx _ (slin_ne_zero A σ (Ω_ne_zero i))
  conv_lhs => rw [hv]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) _

theorem planePerm_slHom (M : Matrix.SpecialLinearGroup (Fin 3) F4) :
    planePerm (slHom M) = pslPerm (M : PSL(3, F4)) :=
  (pslPerm_mk_eq M).symm

noncomputable abbrev P0 : Subgroup (Equiv.Perm (Fin 21)) := pslPerm.range

theorem planePerm_slHom_mem (M : Matrix.SpecialLinearGroup (Fin 3) F4) :
    planePerm (slHom M) ∈ P0 :=
  ⟨_, (planePerm_slHom M).symm⟩

theorem planePerm_conj_mem (g : GammaL3) {p : Equiv.Perm (Fin 21)} (hp : p ∈ P0) :
    planePerm g * p * (planePerm g)⁻¹ ∈ P0 := by
  obtain ⟨q, rfl⟩ := hp
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, hb⟩ := slHom_conj g M
  have e : pslPerm (QuotientGroup.mk M : PSL(3, F4)) = planePerm (slHom M) :=
    (planePerm_slHom M).symm
  rw [e, ← map_inv, ← map_mul, ← map_mul, hb]
  exact planePerm_slHom_mem b

theorem two_lines_through : ∀ i : Fin 21, ∃ a b : Fin 21, a ≠ b ∧ IsOn a i ∧ IsOn b i := by
  decide +kernel

theorem eq_one_of_commute_P0 {σ : Equiv.Perm (Fin 21)} (h : ∀ p ∈ P0, σ * p = p * σ) :
    σ = 1 := by
  have hline : ∀ a : Fin 21, ∀ i : Fin 21, IsOn a i → IsOn a (σ i) := by
    intro a i hi
    obtain ⟨g, -, hg⟩ := exists_elation_projLine a
    have hc := h (pslPerm g) ⟨g, rfl⟩
    have h1 : pslPerm g i = i := (hg i).mpr (mem_projLine.mpr hi)
    have h2 : pslPerm g (σ i) = σ i := by
      calc pslPerm g (σ i) = (pslPerm g * σ) i := rfl
        _ = (σ * pslPerm g) i := by rw [hc]
        _ = σ i := by rw [Equiv.Perm.mul_apply, h1]
    exact mem_projLine.mp ((hg _).mp h2)
  refine Equiv.ext fun i => ?_
  obtain ⟨a, b, hab, ha, hb⟩ := two_lines_through i
  have e1 := meet_unique a b (σ i) hab (hline a i ha) (hline b i hb)
  have e2 := meet_unique a b i hab ha hb
  rw [Equiv.Perm.one_apply]
  exact e1.trans e2.symm

theorem planePerm_eq_one_iff (g : GammaL3) : planePerm g = 1 ↔ rhoGL g = 1 := by
  change ptEquiv.symm.permCongrHom (rhoGL g) = 1 ↔ _
  exact MulEquiv.map_eq_one_iff _

theorem semΓ_mul (A B : GL (Fin 3) F4) (σ τ : F4 ≃+* F4) :
    semΓ A σ * semΓ B τ =
      semΓ (A * Matrix.GeneralLinearGroup.map (σ : F4 →+* F4) B) (τ.trans σ) :=
  Subtype.ext (Equiv.ext fun v => slin_slin A B σ τ v)

theorem semΓ_inv (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) :
    (semΓ A σ)⁻¹ = semΓ (slinInvMat A σ) σ.symm :=
  Subtype.ext (Equiv.ext fun _ => rfl)

theorem semΓ_refl_eq_slHom (B : GL (Fin 3) F4) (hB : (B : Matrix (Fin 3) (Fin 3) F4).det = 1) :
    semΓ B (RingEquiv.refl F4) = slHom ⟨B, hB⟩ :=
  Subtype.ext (Equiv.ext fun _ => rfl)

theorem frobF4_omega : frobF4 F4.ω = F4.ω * F4.ω := rfl

theorem omega_mul_omega_ne_omega : F4.ω * F4.ω ≠ F4.ω := by decide

theorem planePerm_semΓ_frob_not_mem (A : GL (Fin 3) F4) : planePerm (semΓ A frobF4) ∉ P0 := by
  rintro ⟨q, hq⟩
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective q
  have hq' : planePerm (slHom M) = planePerm (semΓ A frobF4) := by
    rw [planePerm_slHom]
    exact hq
  have h1 : planePerm ((slHom M)⁻¹ * semΓ A frobF4) = 1 := by
    rw [map_mul, map_inv, ← hq', inv_mul_cancel]
  obtain ⟨c, hc⟩ := (mem_ker_rhoGL _).mp (MonoidHom.mem_ker.mpr
    ((planePerm_eq_one_iff _).mp h1))
  set g : GammaL3 := (slHom M)⁻¹ * semΓ A frobF4 with hg
  have hlin : ∀ (a : F4) (v : Vec3), ((slHom M)⁻¹ : GammaL3).1 (a • v) =
      a • ((slHom M)⁻¹ : GammaL3).1 v := by
    intro a v
    rw [← map_inv]
    change ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ (a • v) =
      a • (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ v)
    rw [Matrix.mulVec_smul]
  have hgω : ∀ v : Vec3, (g : Equiv.Perm Vec3) (F4.ω • v) =
      (F4.ω * F4.ω) • (g : Equiv.Perm Vec3) v := by
    intro v
    change ((slHom M)⁻¹ : GammaL3).1 (slin A frobF4 (F4.ω • v)) =
      (F4.ω * F4.ω) • ((slHom M)⁻¹ : GammaL3).1 (slin A frobF4 v)
    rw [slin_smul, frobF4_omega, hlin]
  set e0 : Vec3 := Pi.single 0 1 with he0
  have he0ne : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [he0] at this
  have k1 := hc (F4.ω • e0)
  rw [hgω, hc e0, smul_smul, smul_smul] at k1
  have hcne : (c : F4) ≠ 0 := c.ne_zero
  have k2 : (F4.ω * F4.ω * (c : F4) - (c : F4) * F4.ω) • e0 = 0 := by
    rw [sub_smul, k1, sub_self]
  rcases smul_eq_zero.mp k2 with h | h
  · apply omega_mul_omega_ne_omega
    have h' : (F4.ω * F4.ω - F4.ω) * (c : F4) = 0 := by
      rw [sub_mul, mul_comm F4.ω (c : F4)]
      exact h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact sub_eq_zero.mp h''
    · exact absurd h'' hcne
  · exact absurd h he0ne

theorem planePerm_mul_inv_mem (X Y : GL (Fin 3) F4)
    (hXY : (X : Matrix (Fin 3) (Fin 3) F4).det = (Y : Matrix (Fin 3) (Fin 3) F4).det) :
    planePerm (semΓ X frobF4) * (planePerm (semΓ Y frobF4))⁻¹ ∈ P0 := by
  rw [← map_inv, ← map_mul, semΓ_inv, semΓ_mul, RingEquiv.symm_trans_self]
  have hmap : Matrix.GeneralLinearGroup.map (frobF4 : F4 →+* F4) (slinInvMat Y frobF4) = Y⁻¹ := by
    ext i j
    simp only [slinInvMat, Matrix.GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
  rw [hmap]
  have hdet : ((X * Y⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hXY, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.det_one]
  rw [semΓ_refl_eq_slHom _ hdet]
  exact planePerm_slHom_mem _

end CFSG.Quasithin.H13
