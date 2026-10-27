module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Rep4371.Chi
public import CFSG.Monster.B.TwoA.Base.FullCent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.SpinLattice
  CFSG.Monster.Spin CFSG.Monster.ScalarKernel CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA

@[expose] noncomputable def cbarEquiv : Cbar ≃* Shat := MonoidHom.ofInjective iotaD_injective

theorem coe_cbarEquiv (c : Cbar) : (cbarEquiv c : Dfull) = iotaD c := rfl

@[expose] noncomputable def rhoV : Shat →* (Vst ≃ₗ[ℚ] Vst) :=
  chi.comp cbarEquiv.symm.toMonoidHom

theorem rhoV_cbarEquiv (c : Cbar) : rhoV (cbarEquiv c) = chi c := by
  rw [rhoV, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem rhoV_kappa_apply (g : Cgen) (v : Vst) :
    ((rhoV (cbarEquiv (kappa g)) v : Vst) : SpaceB) = (g : SpaceB ≃ₗ[ℚ] SpaceB) v := by
  rw [rhoV_cbarEquiv, coe_chi_kappa_apply]

theorem exists_of_mem_Jhat {h : Dfull} (hh : h ∈ Jhat) :
    ∃ g : Cgen, (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar ∧ iotaD (kappa g) = h := by
  rw [Jhat_eq_map] at hh
  obtain ⟨j, hj, rfl⟩ := hh
  obtain ⟨g, hg, rfl⟩ := hj
  exact ⟨g, hg, rfl⟩

theorem exists_of_mem_Ehat {e : Dfull} (he : e ∈ Ehat) :
    ∃ q, ∃ hq : q ∈ Subgroup.centralizer {rStar},
      iotaD (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) = e := by
  obtain ⟨e₀, he₀, rfl⟩ := he
  obtain ⟨q, hq, hqe⟩ := exists_rep_Ebar ⟨e₀, he₀⟩
  exact ⟨q, hq, congrArg (fun x : Ebar => iotaD (x : Cbar)) hqe.symm⟩

theorem shat_eq_cbarEquiv {h : Dfull} {g : Cgen} (hS : h ∈ Shat) (hg : iotaD (kappa g) = h) :
    (⟨h, hS⟩ : Shat) = cbarEquiv (kappa g) := Subtype.ext hg.symm

@[expose] def blockA : Submodule ℚ SpaceB where
  carrier := {v | v.2.1 = 0 ∧ v.2.2 = 0}
  add_mem' ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c v hv := ⟨by simp [hv.1], by simp [hv.2]⟩

@[expose] def blockX : Submodule ℚ SpaceB where
  carrier := {v | v.1 = 0 ∧ v.2.2 = 0}
  add_mem' ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c v hv := ⟨by simp [hv.1], by simp [hv.2]⟩

@[expose] def blockW : Submodule ℚ SpaceB where
  carrier := {v | v.1 = 0 ∧ v.2.1 = 0}
  add_mem' ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c v hv := ⟨by simp [hv.1], by simp [hv.2]⟩

theorem Across_le_blockA : Across isShortCoord_rStar ≤ blockA := by
  rintro _ ⟨w, -, rfl⟩
  exact ⟨rfl, rfl⟩

theorem Xdiff_le_blockX : Xdiff isShortCoord_rStar ≤ blockX := by
  rw [Xdiff, Submodule.span_le]
  rintro _ ⟨s, -, rfl⟩
  exact ⟨rfl, rfl⟩

theorem Tplus_le_blockW : Tplus isShortCoord_rStar ≤ blockW := by
  rintro _ ⟨q, -, rfl⟩
  exact ⟨rfl, rfl⟩

theorem exists_decomp {v : SpaceB} (hv : v ∈ Vst) :
    ∃ a ∈ Across isShortCoord_rStar, ∃ x ∈ Xdiff isShortCoord_rStar,
      ∃ t ∈ Tplus isShortCoord_rStar, v = a + x + t := by
  rw [Vst, V4_eq_sup isShortCoord_rStar] at hv
  obtain ⟨ax, hax, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨a, ha, x, hx, rfl⟩ := Submodule.mem_sup.1 hax
  exact ⟨a, ha, x, hx, t, ht, rfl⟩

theorem mem_Across_of {v : SpaceB} (hv : v ∈ Vst) (hA : v ∈ blockA) :
    v ∈ Across isShortCoord_rStar := by
  obtain ⟨a, ha, x, hx, t, ht, rfl⟩ := exists_decomp hv
  have hxA := Xdiff_le_blockX hx
  have htA := Tplus_le_blockW ht
  have haA := Across_le_blockA ha
  have hx0 : x = 0 := by
    have h1 : (a + x + t).2.1 = 0 := hA.1
    simp only [Prod.snd_add, Prod.fst_add, haA.1, htA.2, add_zero, zero_add] at h1
    exact Prod.ext hxA.1 (Prod.ext h1 hxA.2)
  have ht0 : t = 0 := by
    have h1 : (a + x + t).2.2 = 0 := hA.2
    simp only [Prod.snd_add, haA.2, hxA.2, zero_add] at h1
    exact Prod.ext htA.1 (Prod.ext htA.2 h1)
  rw [hx0, ht0, add_zero, add_zero]
  exact ha

theorem mem_Xdiff_of {v : SpaceB} (hv : v ∈ Vst) (hX : v ∈ blockX) :
    v ∈ Xdiff isShortCoord_rStar := by
  obtain ⟨a, ha, x, hx, t, ht, rfl⟩ := exists_decomp hv
  have hxA := Xdiff_le_blockX hx
  have htA := Tplus_le_blockW ht
  have haA := Across_le_blockA ha
  have ha0 : a = 0 := by
    have h1 : (a + x + t).1 = 0 := hX.1
    simp only [Prod.fst_add, hxA.1, htA.1, add_zero] at h1
    exact Prod.ext h1 (Prod.ext haA.1 haA.2)
  have ht0 : t = 0 := by
    have h1 : (a + x + t).2.2 = 0 := hX.2
    simp only [Prod.snd_add, haA.2, hxA.2, zero_add] at h1
    exact Prod.ext htA.1 (Prod.ext htA.2 h1)
  rw [ha0, ht0, add_zero, zero_add]
  exact hx

theorem mem_Tplus_of {v : SpaceB} (hv : v ∈ Vst) (hW : v ∈ blockW) :
    v ∈ Tplus isShortCoord_rStar := by
  obtain ⟨a, ha, x, hx, t, ht, rfl⟩ := exists_decomp hv
  have hxA := Xdiff_le_blockX hx
  have htA := Tplus_le_blockW ht
  have haA := Across_le_blockA ha
  have ha0 : a = 0 := by
    have h1 : (a + x + t).1 = 0 := hW.1
    simp only [Prod.fst_add, hxA.1, htA.1, add_zero] at h1
    exact Prod.ext h1 (Prod.ext haA.1 haA.2)
  have hx0 : x = 0 := by
    have h1 : (a + x + t).2.1 = 0 := hW.2
    simp only [Prod.snd_add, Prod.fst_add, haA.1, htA.2, add_zero, zero_add] at h1
    exact Prod.ext hxA.1 (Prod.ext h1 hxA.2)
  rw [ha0, hx0, add_zero, zero_add]
  exact ht

theorem theta_mem_blockA (p : Pvis) {v : SpaceB} (hv : v ∈ blockA) : theta p v ∈ blockA := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩ <;> rw [theta_apply]
  · show thetaX p v.2.1 = 0
    rw [h1, map_zero]
  · show thetaW _ _ v.2.2 = 0
    rw [h2, map_zero]

theorem theta_mem_blockX (p : Pvis) {v : SpaceB} (hv : v ∈ blockX) : theta p v ∈ blockX := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩ <;> rw [theta_apply]
  · show thetaA _ v.1 = 0
    rw [h1, map_zero]
  · show thetaW _ _ v.2.2 = 0
    rw [h2, map_zero]

theorem theta_mem_blockW (p : Pvis) {v : SpaceB} (hv : v ∈ blockW) : theta p v ∈ blockW := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩ <;> rw [theta_apply]
  · show thetaA _ v.1 = 0
    rw [h1, map_zero]
  · show thetaX p v.2.1 = 0
    rw [h2, map_zero]

@[expose] noncomputable def V23 : Submodule ℚ Vst := (Across isShortCoord_rStar).comap Vst.subtype

@[expose] noncomputable def V2300 : Submodule ℚ Vst := (Xdiff isShortCoord_rStar).comap Vst.subtype

@[expose] noncomputable def V2048 : Submodule ℚ Vst := (Tplus isShortCoord_rStar).comap Vst.subtype

theorem mem_V23 {v : Vst} : v ∈ V23 ↔ (v : SpaceB) ∈ Across isShortCoord_rStar := Iff.rfl
theorem mem_V2300 {v : Vst} : v ∈ V2300 ↔ (v : SpaceB) ∈ Xdiff isShortCoord_rStar := Iff.rfl
theorem mem_V2048 {v : Vst} : v ∈ V2048 ↔ (v : SpaceB) ∈ Tplus isShortCoord_rStar := Iff.rfl

theorem Jhat_preserves {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    (∀ v ∈ V23, rhoV h v ∈ V23) ∧ (∀ v ∈ V2300, rhoV h v ∈ V2300) ∧
      ∀ v ∈ V2048, rhoV h v ∈ V2048 := by
  obtain ⟨g, hg, hgh⟩ := exists_of_mem_Jhat hh
  obtain ⟨p, hp⟩ := mem_Gvis.1 hg.1
  have e : h = cbarEquiv (kappa g) := Subtype.ext hgh.symm
  have key : ∀ v : Vst, ((rhoV h v : Vst) : SpaceB) = theta p v := by
    intro v
    rw [e, rhoV_kappa_apply, ← hp]
    rfl
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_V23, key]
    exact mem_Across_of (by rw [← key]; exact (rhoV h v).2)
      (theta_mem_blockA p (Across_le_blockA hv))
  · rw [mem_V2300, key]
    exact mem_Xdiff_of (by rw [← key]; exact (rhoV h v).2)
      (theta_mem_blockX p (Xdiff_le_blockX hv))
  · rw [mem_V2048, key]
    exact mem_Tplus_of (by rw [← key]; exact (rhoV h v).2)
      (theta_mem_blockW p (Tplus_le_blockW hv))

theorem rhoV_Ehat_apply
    {e : Shat} {q : Q} (hq : q ∈ Subgroup.centralizer {rStar})
    (he : iotaD (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) = e) (v : Vst) :
    ((rhoV e v : Vst) : SpaceB) = theta (rhoPair q) v := by
  have e' : e = cbarEquiv (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) := Subtype.ext he.symm
  rw [e', rhoV_kappa_apply]
  rfl

theorem theta_rhoPair_inA (q : Q) (A : symMat) : theta (rhoPair q) (A, 0, 0) = (A, 0, 0) := by
  rw [theta_symMat]
  refine Prod.ext (Subtype.ext ?_) rfl
  show Matrix.transpose (mat (1 : latticeO)) * (A : Matrix (Fin 24) (Fin 24) ℚ) * mat 1 = A
  rw [mat_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem Ehat_trivial_V23
    {e : Shat} (he : (e : Dfull) ∈ Ehat) {v : Vst} (hv : v ∈ V23) :
    rhoV e v = v := by
  obtain ⟨q, hq, hqe⟩ := exists_of_mem_Ehat he
  apply Subtype.ext
  rw [rhoV_Ehat_apply hq hqe]
  have key : ∀ w : SpaceB, w ∈ blockA → theta (rhoPair q) w = w := by
    rintro ⟨A, X, N⟩ ⟨hX, hN⟩
    simp only at hX hN
    subst hX
    subst hN
    exact theta_rhoPair_inA q A
  exact key _ (Across_le_blockA hv)

end CFSG.Monster.B.CTIB
