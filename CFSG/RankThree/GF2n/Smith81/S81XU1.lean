module

public import CFSG.RankThree.GF2n.Smith81.S81UFrame
public import CFSG.RankThree.GF2n.Smith81.S81JSpecial

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

section FrameDict

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {ω : F}

@[expose] noncomputable def ucF (σ : F ≃+* F) (hω : ω + σ ω = 1) (g : GL (Fin 6) F) :
    GL (Fin 6) F :=
  (frameGL σ ω hω)⁻¹ * g * frameGL σ ω hω

@[expose] noncomputable def kdimU (σ : F ≃+* F) (hω : ω + σ ω = 1) (g : GL (Fin 6) F) : ℕ :=
  Module.finrank F ↥(imgS0 (ucF σ hω g) ⊓ S0 F)

theorem ucF_mul (hω : ω + σ ω = 1) (g h : GL (Fin 6) F) :
    ucF σ hω (g * h) = ucF σ hω g * ucF σ hω h := by
  simp only [ucF]
  group

theorem ucF_inv (hω : ω + σ ω = 1) (g : GL (Fin 6) F) :
    ucF σ hω g⁻¹ = (ucF σ hω g)⁻¹ := by
  simp only [ucF]
  group

theorem ucF_eq_one_iff (hω : ω + σ ω = 1) (g : GL (Fin 6) F) : ucF σ hω g = 1 ↔ g = 1 := by
  constructor
  · intro h
    have h' : frameGL σ ω hω * ucF σ hω g * (frameGL σ ω hω)⁻¹ = g := by
      simp only [ucF]
      group
    rw [← h', h]
    group
  · rintro rfl
    simp [ucF]

theorem ucF_det (hω : ω + σ ω = 1) {g : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F).det = 1) :
    ((ucF σ hω g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 := by
  simp only [ucF, Units.val_mul, Matrix.det_mul, hg, mul_one]
  rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

theorem rho_pt0_ucF (hω : ω + σ ω = 1) (g : GL (Fin 6) F) :
    rho F g (pt0 F) = rho F (frameGL σ ω hω) (rho F (ucF σ hω g) (p0 F)) := by
  rw [← rho_mul_apply]
  have h : frameGL σ ω hω * ucF σ hω g = g * frameGL σ ω hω := by
    simp only [ucF]
    group
  rw [h, rho_mul_apply, rho_frameGL_p0 ω hω]

theorem beta_pt0_rho_eq_zero_iff (hω : ω + σ ω = 1) {g : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F).det = 1) :
    beta F (pt0 F) (rho F g (pt0 F)) = 0 ↔ 1 ≤ kdimU σ hω g := by
  have hpt : pt0 F = rho F (frameGL σ ω hω) (p0 F) := (rho_frameGL_p0 ω hω).symm
  have h1 : beta F (pt0 F) (rho F g (pt0 F)) =
      ((frameGL σ ω hω : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det *
        beta F (p0 F) (rho F (ucF σ hω g) (p0 F)) := by
    have e1 := rho_pt0_ucF hω g
    calc beta F (pt0 F) (rho F g (pt0 F))
        = beta F (rho F (frameGL σ ω hω) (p0 F))
            (rho F (frameGL σ ω hω) (rho F (ucF σ hω g) (p0 F))) := by
          rw [← e1, ← hpt]
      _ = _ := beta_rho _ _ _
  have hdet : ((frameGL σ ω hω : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det ≠ 0 :=
    (Matrix.isUnits_det_units (frameGL σ ω hω)).ne_zero
  rw [h1, mul_eq_zero, or_iff_right hdet]
  exact beta_rho_p0_eq_zero_iff (ucF_det hω hg)

end FrameDict

section Transvec

variable {F : Type} [Field F]

theorem u6_isTransvec_of_inter {S S' : Submodule F (Fin 6 → F)} {τ : GL (Fin 6) F}
    (hτ : τ ∈ UnipGL F S ⊓ UnipGL F S') (hL : Module.finrank F ↥(S ⊓ S') = 1) (hne : τ ≠ 1) :
    IsTransvec F τ := by
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 6) (Fin 6) F, N = (τ : Matrix (Fin 6) (Fin 6) F) - 1 :=
    ⟨_, rfl⟩
  have hNv : ∀ v : Fin 6 → F, N.mulVec v = (τ : Matrix (Fin 6) (Fin 6) F).mulVec v - v := by
    intro v
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hmem : ∀ v : Fin 6 → F, N.mulVec v ∈ S ⊓ S' := by
    intro v
    rw [hNv]
    exact inf_UnipGL_sub_mem hτ v
  have hfix : ∀ v : Fin 6 → F,
      (τ : Matrix (Fin 6) (Fin 6) F).mulVec (N.mulVec v) = N.mulVec v := by
    intro v
    exact inf_UnipGL_fix_sup hτ ((inf_le_left.trans le_sup_left : S ⊓ S' ≤ S ⊔ S') (hmem v))
  have hNN : N * N = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, hNv (N.mulVec v), hfix v, sub_self]
  have hN0 : N ≠ 0 := by
    intro h0
    apply hne
    apply Units.ext
    rw [Units.val_one]
    rw [hN, sub_eq_zero] at h0
    exact h0
  have hex : ∃ v : Fin 6 → F, N.mulVec v ≠ 0 := by
    by_contra hcon
    apply hN0
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.zero_mulVec]
    by_contra hv
    exact hcon ⟨v, hv⟩
  have hrank_pos : 0 < Matrix.rank N := by
    obtain ⟨v, hv⟩ := hex
    unfold Matrix.rank
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨N.mulVec v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hrank_le : Matrix.rank N ≤ 1 := by
    have hle : LinearMap.range N.mulVecLin ≤ S ⊓ S' := by
      rintro _ ⟨v, rfl⟩
      exact hmem v
    have h := Submodule.finrank_mono hle
    rw [hL] at h
    exact h
  unfold IsTransvec
  rw [← hN]
  exact ⟨hNN, by omega⟩

end Transvec

section WDict

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {ω : F} {K : Type} [Field K]
  {e : K ≃+* Fσ σ}

private theorem u6x_val_sub (x y : E3UWspace σ e) : e3uVal (x - y) = e3uVal x - e3uVal y := rfl

private theorem u6x_val_smul (c : K) (x : E3UWspace σ e) :
    e3uVal (c • x) = ((e c : Fσ σ) : F) • e3uVal x := rfl

private theorem u6x_val_p0 : e3uVal (e3uP0 σ e) = pt0 F := rfl

private theorem u6x_val_mem (x : E3UWspace σ e) : e3uVal x ∈ Wsub σ :=
  mem_Wform_iff.mp (show Wform σ from x).2

private theorem u6x_inj {x y : E3UWspace σ e} (h : e3uVal x = e3uVal y) : x = y :=
  Subtype.ext h

theorem u6_mem_span_p0_of_val (hσ : ∀ c, σ (σ c) = c) {y : E3UWspace σ e} {c : F}
    (h : e3uVal y = c • pt0 F) : y ∈ Submodule.span K {e3uP0 σ e} := by
  have hσc : σ c = c :=
    smul_mem_Fq_of_mem_Wsub hσ (u6x_val_mem y) (mem_Wsub_iff.mpr theta_pt0) pt0_ne_zero h
  have hcmem : c ∈ Fσ σ := mem_Fσ_iff.mpr hσc
  rw [Submodule.mem_span_singleton]
  refine ⟨e.symm ⟨c, hcmem⟩, u6x_inj ?_⟩
  have hek : ((e (e.symm ⟨c, hcmem⟩) : Fσ σ) : F) = c :=
    congrArg Subtype.val (e.apply_symm_apply ⟨c, hcmem⟩)
  rw [u6x_val_smul, hek, h, u6x_val_p0]

theorem u6_wact_mem_W0 (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1) (g : SUid σ 6)
    (hk : 2 ≤ kdimU σ hω (g : GL (Fin 6) F)) :
    e3uWact σ e g (e3uP0 σ e) ∈ Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e) := by
  rw [mem_Wsp]
  intro u hu
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp (show u ∈ (e3uU0Sub σ).map (e3uWact σ e) from hu)
  have hdetg : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 :=
    ((CFSG.ClassicalGroups.Unitary.mem_SUid_iff σ).mp g.2).1
  have hW0 : rho F (ucF σ hω (g : GL (Fin 6) F)) (p0 F) ∈
      Wsp (Submodule.span F {p0 F}) (U0 F) :=
    (rho_p0_mem_W0_iff (ucF_det hω hdetg)).mpr hk
  have hUg' : rhoEquiv F (ucF σ hω (g' : GL (Fin 6) F)) ∈ U0 F := by
    rw [U0_eq_Urad]
    exact Subgroup.mem_map_of_mem (rhoEquiv F) (frame_conj_unip_of_mem_U0Sub hσ hω hg')
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (mem_Wsp.mp hW0 _ hUg')
  refine u6_mem_span_p0_of_val hσ.invol (c := c) ?_
  have hS : rho F (frameGL σ ω hω) (p0 F) = pt0 F := rho_frameGL_p0 ω hω
  have h1 : rho F (g' : GL (Fin 6) F) (rho F (g : GL (Fin 6) F) (pt0 F)) =
      rho F (frameGL σ ω hω) (rho F (ucF σ hω (g' : GL (Fin 6) F))
        (rho F (ucF σ hω (g : GL (Fin 6) F)) (p0 F))) := by
    rw [← rho_mul_apply, rho_pt0_ucF hω (g' * g), ucF_mul, rho_mul_apply]
  have h2 := congrArg (rho F (frameGL σ ω hω)) hc
  simp only [rhoEquiv_apply, map_smul, map_sub, hS] at h2
  rw [u6x_val_sub, e3uWact_val, e3uWact_val, u6x_val_p0, h1, rho_pt0_ucF hω g]
  exact h2.symm

theorem u6_transvec_of_kdim_one (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1)
    (e : K ≃+* Fσ σ) {g ũ ũ₂ : SUid σ 6} (hũ : ũ ∈ e3uU0Sub σ) (hũ₂ : ũ₂ ∈ e3uU0Sub σ)
    (heq : e3uWact σ e ũ = e3uWact σ e (g * ũ₂ * g⁻¹))
    (hk : kdimU σ hω (g : GL (Fin 6) F) = 1) (hne : (ũ : GL (Fin 6) F) ≠ 1) :
    IsTransvec F (ũ : GL (Fin 6) F) := by
  set S : GL (Fin 6) F := frameGL σ ω hω with hSdef
  have hone : e3uWact σ e (ũ * (g * ũ₂ * g⁻¹)⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  obtain ⟨l, -, hl⟩ := (e3uWact_eq_one_iff hσ _).mp hone
  have hũeq : ((ũ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      l • (((g * ũ₂ * g⁻¹ : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    have h1 : ((ũ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        ((ũ * (g * ũ₂ * g⁻¹)⁻¹ * (g * ũ₂ * g⁻¹) : SUid σ 6) : GL (Fin 6) F) := by
      rw [inv_mul_cancel_right]
    rw [h1]
    simp only [Subgroup.coe_mul, Units.val_mul]
    simp only [Subgroup.coe_mul, Units.val_mul] at hl
    rw [hl, Matrix.smul_mul, Matrix.one_mul]
  have hU₁ : ucF σ hω (ũ : GL (Fin 6) F) ∈ UnipGL F (S0 F) :=
    frame_conj_unip_of_mem_U0Sub hσ hω hũ
  have hU₂ : ucF σ hω (ũ₂ : GL (Fin 6) F) ∈ UnipGL F (S0 F) :=
    frame_conj_unip_of_mem_U0Sub hσ hω hũ₂
  have hU₂' : ucF σ hω ((g * ũ₂ * g⁻¹ : SUid σ 6) : GL (Fin 6) F) ∈
      UnipGL F (imgS0 (ucF σ hω (g : GL (Fin 6) F))) := by
    have h := s81A12_conj_mem (ucF σ hω (g : GL (Fin 6) F)) (S0 F) hU₂
    have e1 : ucF σ hω ((g * ũ₂ * g⁻¹ : SUid σ 6) : GL (Fin 6) F) =
        ucF σ hω (g : GL (Fin 6) F) * ucF σ hω (ũ₂ : GL (Fin 6) F) *
          (ucF σ hω (g : GL (Fin 6) F))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ucF_mul, ucF_inv]
    rw [e1]
    exact h
  have hpos : 0 < Module.finrank F ↥(imgS0 (ucF σ hω (g : GL (Fin 6) F)) ⊓ S0 F) := by
    have h : kdimU σ hω (g : GL (Fin 6) F) = Module.finrank F ↥(imgS0 (ucF σ hω (g : GL (Fin 6) F)) ⊓ S0 F) := rfl
    omega
  have hne_bot : imgS0 (ucF σ hω (g : GL (Fin 6) F)) ⊓ S0 F ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  obtain ⟨hvS, hvS0⟩ := Submodule.mem_inf.mp hv
  have f1 : ((ucF σ hω (ũ : GL (Fin 6) F) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec v =
      v := UnipGL_fix hU₁ hvS0
  have f2 : ((ucF σ hω ((g * ũ₂ * g⁻¹ : SUid σ 6) : GL (Fin 6) F) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F).mulVec v = v := UnipGL_fix hU₂' hvS
  have hmat : ((ucF σ hω (ũ : GL (Fin 6) F) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      l • ((ucF σ hω ((g * ũ₂ * g⁻¹ : SUid σ 6) : GL (Fin 6) F) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) := by
    simp only [ucF, Units.val_mul]
    rw [hũeq, Matrix.mul_smul, Matrix.smul_mul]
  have hl1 : l = 1 := by
    have h1 : l • v = v := by
      have h2 := f1
      rw [hmat, Matrix.smul_mulVec, f2] at h2
      exact h2
    have h3 : (l - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 hv0
  have hucEq : ucF σ hω (ũ : GL (Fin 6) F) =
      ucF σ hω ((g * ũ₂ * g⁻¹ : SUid σ 6) : GL (Fin 6) F) := by
    apply Units.ext
    rw [hmat, hl1, one_smul]
  have hmem : ucF σ hω (ũ : GL (Fin 6) F) ∈ UnipGL F (S0 F) ⊓
      UnipGL F (imgS0 (ucF σ hω (g : GL (Fin 6) F))) :=
    Subgroup.mem_inf.mpr ⟨hU₁, hucEq ▸ hU₂'⟩
  have hL : Module.finrank F ↥(S0 F ⊓ imgS0 (ucF σ hω (g : GL (Fin 6) F))) = 1 := by
    rw [inf_comm]
    exact hk
  have hne' : ucF σ hω (ũ : GL (Fin 6) F) ≠ 1 := fun h => hne ((ucF_eq_one_iff hω _).mp h)
  have hT := u6_isTransvec_of_inter hmem hL hne'
  have hback : (ũ : GL (Fin 6) F) = S * ucF σ hω (ũ : GL (Fin 6) F) * S⁻¹ := by
    simp only [ucF, hSdef]
    group
  rw [hback]
  exact IsTransvec.conj' hT S

theorem frameInv_mulVec_T0 (hω : ω + σ ω = 1) (j : Fin 3) :
    ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F).val.mulVec (e3uT0Vec j) =
      Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F) := by
  have h1 : ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F).val = frameInv σ ω := rfl
  rw [h1, ← frameMat_mulVec_even (σ := σ) ω j, Matrix.mulVec_mulVec, frameInv_mul_frameMat hω,
    Matrix.one_mulVec]

theorem mem_e3uU0Sub_iff (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1) (g : SUid σ 6) :
    g ∈ e3uU0Sub σ ↔ ∀ s ∈ S0 F, ((ucF σ hω (g : GL (Fin 6) F) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F).mulVec s = s := by
  constructor
  · intro hg
    exact fun s hs => UnipGL_fix (frame_conj_unip_of_mem_U0Sub hσ hω hg) hs
  · intro h j
    have hj : (Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F)) ∈ S0 F :=
      s81A12_single_mem_S0 (by simp) 1
    have h1 := h _ hj
    show ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec j) = e3uT0Vec j
    have e1 : (e3uT0Vec j : Fin 6 → F) = (frameGL σ ω hω : GL (Fin 6) F).val.mulVec
        (Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F)) :=
      (frameMat_mulVec_even (σ := σ) ω j).symm
    rw [e1, Matrix.mulVec_mulVec]
    have e2 : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (frameGL σ ω hω : GL (Fin 6) F).val =
        (frameGL σ ω hω : GL (Fin 6) F).val *
          ((ucF σ hω (g : GL (Fin 6) F) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
      have : (g : GL (Fin 6) F) * frameGL σ ω hω =
          frameGL σ ω hω * ucF σ hω (g : GL (Fin 6) F) := by
        simp only [ucF]
        group
      exact congrArg Units.val this
    rw [e2, ← Matrix.mulVec_mulVec, h1]

theorem imgS0_ucF_eq (hω : ω + σ ω = 1) {h : GL (Fin 6) F} {c : F} (hc : c ≠ 0)
    (hh : rho F h (pt0 F) = c • pt0 F) : imgS0 (ucF σ hω h) = S0 F := by
  apply imgS0_eq_of_rho_p0 hc
  have e1 := rho_pt0_ucF hω h
  rw [hh, ← rho_frameGL_p0 ω hω, ← map_smul] at e1
  have hinj : Function.Injective (rho F (frameGL σ ω hω)) := by
    intro x y hxy
    have h2 := congrArg (rho F (frameGL σ ω hω)⁻¹) hxy
    rw [← rho_mul_apply, ← rho_mul_apply, inv_mul_cancel, rho_one] at h2
    exact h2
  exact hinj e1.symm

theorem conj_mem_e3uU0Sub (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1) {h : SUid σ 6} {c : F}
    (hc : c ≠ 0) (hh : rho F (h : GL (Fin 6) F) (pt0 F) = c • pt0 F) {u : SUid σ 6}
    (hu : u ∈ e3uU0Sub σ) : h * u * h⁻¹ ∈ e3uU0Sub σ := by
  have himg := imgS0_ucF_eq hω hc hh
  have hfix := (mem_e3uU0Sub_iff hσ hω u).mp hu
  rw [mem_e3uU0Sub_iff hσ hω]
  intro s hs
  have hs' : s ∈ imgS0 (ucF σ hω (h : GL (Fin 6) F)) := himg ▸ hs
  obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp hs'
  have hts' : ((ucF σ hω (h : GL (Fin 6) F) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec t = s :=
    hts
  have htS0 : t ∈ S0 F := ht
  have hinv : ((ucF σ hω (h : GL (Fin 6) F))⁻¹ : GL (Fin 6) F).val.mulVec s = t := by
    rw [← hts', Matrix.mulVec_mulVec]
    simp
  have e1 : ucF σ hω ((h * u * h⁻¹ : SUid σ 6) : GL (Fin 6) F) =
      ucF σ hω (h : GL (Fin 6) F) * ucF σ hω (u : GL (Fin 6) F) *
        (ucF σ hω (h : GL (Fin 6) F))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ucF_mul, ucF_inv]
  rw [e1]
  simp only [Units.val_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, hfix t htS0, hts']

private theorem u6x_val_wact_p0 (h : SUid σ 6) :
    e3uVal (e3uWact σ e h (e3uP0 σ e)) = rho F (h : GL (Fin 6) F) (pt0 F) := by
  rw [e3uWact_val, u6x_val_p0]

theorem u6_U_norm (hσ : IsUnitaryInvolution σ) (hω : ω + σ ω = 1) (e : K ≃+* Fσ σ) :
    ∀ h ∈ e3uGam σ e, (∃ c : K, c ≠ 0 ∧ h (e3uP0 σ e) = c • e3uP0 σ e) →
      conjSub h (e3uU0 σ e) = e3uU0 σ e := by
  rintro h hh ⟨c, hc, hpc⟩
  obtain ⟨ĥ, rfl⟩ := MonoidHom.mem_range.mp (show h ∈ (e3uWact σ e).range from hh)
  have hcF : ((e c : Fσ σ) : F) ≠ 0 := by
    intro h0
    apply hc
    apply e.injective
    rw [map_zero]
    exact Subtype.ext h0
  have hrho : rho F (ĥ : GL (Fin 6) F) (pt0 F) = ((e c : Fσ σ) : F) • pt0 F := by
    have h1 := congrArg e3uVal hpc
    rwa [u6x_val_wact_p0, u6x_val_smul, u6x_val_p0] at h1
  have hrho' : rho F ((ĥ⁻¹ : SUid σ 6) : GL (Fin 6) F) (pt0 F) =
      (((e c : Fσ σ) : F))⁻¹ • pt0 F := by
    have h2 := congrArg (rho F ((ĥ⁻¹ : SUid σ 6) : GL (Fin 6) F)) hrho
    rw [← rho_mul_apply, Subgroup.coe_inv, inv_mul_cancel, rho_one, map_smul] at h2
    rw [← Subgroup.coe_inv] at h2
    have h3 : (((e c : Fσ σ) : F))⁻¹ • (pt0 F : Cube F) =
        (((e c : Fσ σ) : F))⁻¹ • (((e c : Fσ σ) : F) • rho F ((ĥ⁻¹ : SUid σ 6) : GL (Fin 6) F) (pt0 F)) := by
      rw [← h2]
      rfl
    rw [h3, smul_smul, inv_mul_cancel₀ hcF, one_smul]
  apply le_antisymm
  · intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := mem_conjSub.mp hu
    obtain ⟨ũ, hũ, rfl⟩ := Subgroup.mem_map.mp (show u₀ ∈ (e3uU0Sub σ).map (e3uWact σ e) from hu₀)
    exact Subgroup.mem_map.mpr ⟨ĥ * ũ * ĥ⁻¹, conj_mem_e3uU0Sub hσ hω hcF hrho hũ,
      by simp only [map_mul, map_inv]⟩
  · intro u hu
    obtain ⟨ũ, hũ, rfl⟩ := Subgroup.mem_map.mp (show u ∈ (e3uU0Sub σ).map (e3uWact σ e) from hu)
    rw [mem_conjSub]
    have hmem : ĥ⁻¹ * ũ * ĥ⁻¹⁻¹ ∈ e3uU0Sub σ :=
      conj_mem_e3uU0Sub hσ hω (inv_ne_zero hcF) hrho' hũ
    rw [inv_inv] at hmem
    refine ⟨e3uWact σ e (ĥ⁻¹ * ũ * ĥ), Subgroup.mem_map_of_mem _ hmem, ?_⟩
    simp only [map_mul, map_inv]
    group

end WDict

end CFSG.RankThree.GF2n.Smith81
