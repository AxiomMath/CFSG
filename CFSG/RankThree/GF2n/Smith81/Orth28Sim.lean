module

public import CFSG.RankThree.GF2n.Smith81.Orth28Route
public import CFSG.RankThree.GF2n.Smith81.Orth28Omega
public import CFSG.RankThree.GF2n.Smith81.OrthRootBack
public import CFSG.RankThree.GF2n.Smith81.OrthRootLA
public import CFSG.RankThree.GF2n.Smith81.Orth52
public import CFSG.RankThree.GF2n.Smith81.OrthSegre

public section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G]

@[expose] def OrthSim {M Q Z B : Subgroup G} (C : OrthCtx M Q Z B) : Prop :=
  ∀ m ∈ H0 M Z, ∃ (g : Matrix (Fin 2) (Fin 2) C.K) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K))
    (ρ : C.K), g.det ≠ 0 ∧ ρ ≠ 0 ∧ (∀ v, C.qU (o v) = ρ * C.qU v) ∧
      ActsAsTensor Q Z C.M₀ C.φ m g o

section Sim

variable [Finite G]

theorem exists_root_of_ctx {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∃ x ∈ Q, x ∉ Z ∧ IsConj z x := by
  have H := hc.hyp
  obtain ⟨g, hg⟩ := hc.conj
  have hBne : B ≠ ⊥ := by
    intro h
    have h1 := card_conjSubgroup g Z
    rw [← hg, h, Subgroup.card_bot] at h1
    have := H.q4
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have haB : (a : G) ∈ B := a.2
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haZ : (a : G) ∉ Z := by
    intro h
    have hm : (a : G) ∈ Z ⊓ B := ⟨h, haB⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at hm
    exact ha1' hm
  have hz : g⁻¹ * (a : G) * g ∈ Z := mem_conjSubgroup.mp (hg ▸ haB)
  refine ⟨g⁻¹ * (a : G) * g, hz, ?_, a, hc.le haB, haZ, ?_⟩
  · intro h
    apply ha1'
    have : (a : G) = g * (g⁻¹ * (a : G) * g) * g⁻¹ := by group
    rw [this, h]; group
  · exact isConj_iff.mpr ⟨g, by group⟩

theorem exists_singular_of_ctx {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) (C : OrthCtx M Q Z B) :
    ∃ u : C.ι → C.K, u ≠ 0 ∧ C.qU u = 0 := by
  obtain ⟨z, hz, hz1, x, hxQ, hxZ, hxc⟩ := exists_root_of_ctx hc
  obtain ⟨c₁, c₂, u, -, hu0, hu, -⟩ := (C.hF.root z hz hz1 x hxQ hxZ).mp hxc
  exact ⟨u, hu0, hu⟩

theorem orthSim_of_dim {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (hdim : Fintype.card C.ι ≠ 4 ∨ NoTotallySingularPlane C.qU) : OrthSim C := by
  intro m hm
  have H := hc.ctx.hyp
  obtain ⟨hmM, hmZ⟩ := hm
  have hcen : ∀ z ∈ Z, m * z * m⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp hmZ z hz
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  obtain ⟨σ, g, o, ρ, hg, hρ, hbij, hadd, hsmul, hq, hact⟩ := orthCoords_sim_of_act C.hF C.hD
    (fun m hm x hx => conj_mem_Q H hm hx) (exists_root_of_ctx hc.ctx) hdim m hmM
  obtain ⟨T, hTπ, -, -⟩ := C.hD.linear_of_centralizes hmM hcen
  obtain ⟨u, hu0, -⟩ := exists_singular_of_ctx hc.ctx C
  have hlin : ∀ (c : C.K) (p : (C.ι → C.K) × (C.ι → C.K)),
      orthTensor g o (c • p) = c • orthTensor g o p := by
    intro c p
    obtain ⟨x, hx, rfl⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) p
    obtain ⟨x', hx', hxe⟩ := C.M₀.π_surj (c • C.M₀.π x)
    have h1 : C.φ (C.M₀.π x') = c • C.φ (C.M₀.π x) := by rw [hxe, map_smul]
    have e1 : C.φ (C.M₀.π (m * x' * m⁻¹)) = orthTensor g o (c • C.φ (C.M₀.π x)) := by
      rw [hact x' hx', h1]
    have e2 : C.φ (C.M₀.π (m * x' * m⁻¹)) = c • C.φ (C.M₀.π (m * x * m⁻¹)) := by
      rw [hTπ x' hx', hxe, map_smul, map_smul, ← hTπ x hx]
    rw [← e1, e2, hact x hx]
  have h0 : o 0 = 0 := by simpa using hsmul 0 u
  have hou : o u ≠ 0 := fun h => hu0 (hbij.1 (h.trans h0.symm))
  have hσ : ∀ c : C.K, σ c = c := by
    intro c
    have hl := hlin c (u, 0)
    have h1 := congrArg Prod.fst hl
    have h2 := congrArg Prod.snd hl
    simp only [orthTensor, Prod.smul_mk, smul_zero, h0, add_zero, hsmul] at h1 h2
    have k1 : (g 0 0 * (σ c - c)) • o u = 0 := by linear_combination (norm := module) h1
    have k2 : (g 1 0 * (σ c - c)) • o u = 0 := by linear_combination (norm := module) h2
    have k1' := (smul_eq_zero.mp k1).resolve_right hou
    have k2' := (smul_eq_zero.mp k2).resolve_right hou
    by_cases hg00 : g 0 0 = 0
    · have hg10 : g 1 0 ≠ 0 := by
        intro h
        apply hg
        rw [Matrix.det_fin_two, hg00, h]
        ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp k2').resolve_left hg10)
    · exact sub_eq_zero.mp ((mul_eq_zero.mp k1').resolve_left hg00)
  let o' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K) := LinearEquiv.ofBijective
    { toFun := o, map_add' := hadd, map_smul' := fun c u => by rw [hsmul, hσ]; rfl } hbij
  refine ⟨g, o', ρ, hg, hρ, fun v => ?_, hact⟩
  show C.qU (o v) = ρ * C.qU v
  rw [hq, hσ]

end Sim

section LgenAct

open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open CFSG.RankThree.GF2n.Stroth80.Classify (pointRad orthSubgroup orthSubgroup_eq_orthogonalGroup
  mem_elementaryGroup_of_mem_pointRad)

variable [Finite G]

theorem four_le_card_of_cfg {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) : 4 ≤ Fintype.card C.ι := by
  obtain ⟨n, hw', -, h4⟩ := hc.orth.exists_width
  have hZ : 2 ≤ Nat.card Z := by have := hc.ctx.hyp.q4; omega
  rw [width_eq_of_width hZ (width_of_tensor C.hD C.φ) hw']
  exact h4

theorem omegaGroup_le_elementaryGroup_of_cfg {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) :
    OrthogonalInvolutions.omegaGroup C.qU (polarBilin_nondegenerate_of_hnd C.hF.nondeg) ≤
      elementaryGroup C.qU :=
  omegaGroup_le_elementaryGroup_of_four_le _
    (by rw [Module.finrank_fintype_fun_eq_card]; exact four_le_card_of_cfg hc C)

theorem actsAsTensor_of_change {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)} (h : GL (Fin 2) K)
    (hdet : (h : Matrix (Fin 2) (Fin 2) K).det = 1) {s : G} {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g.det = 1) {o : (ι → K) ≃ₗ[K] (ι → K)}
    (hs : ActsAsTensor Q Z M₀ (φ.trans (orthTensorEquiv h)) s g o) :
    ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧ ActsAsTensor Q Z M₀ φ s g' o := by
  have hdet' : ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    det_units_inv_eq_one h hdet
  have hback : (φ.trans (orthTensorEquiv h)).trans (orthTensorEquiv h⁻¹) = φ := by
    refine LinearEquiv.ext fun e => ?_
    show orthTensor _ id (orthTensor _ id (φ e)) = φ e
    rw [orthTensor_id_comp, Units.inv_mul, orthTensor_one_id]
  have hc := hs.change h⁻¹ (fun x y => map_add o x y) (fun c x => map_smul o c x)
  rw [hback] at hc
  refine ⟨_, ?_, hc⟩
  simp only [Matrix.det_mul, hdet', hg, det_units_inv_eq_one h⁻¹ hdet', one_mul, mul_one]

theorem lA_act_elementary {M Q Z B A : Subgroup G} (hcB : Ctx M Q Z B) (hcA : Ctx M Q Z A)
    (hno : NoA2 Q Z (LB M Q A)) (hLA : LB M Q A ≤ Lgen M (LB M Q B)) (C : OrthCtx M Q Z B)
    (hn : 4 ≤ Fintype.card C.ι) {t : G} (ht : t ∈ LB M Q A) :
    ∃ (g : Matrix (Fin 2) (Fin 2) C.K) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)), g.det = 1 ∧
      o ∈ elementaryGroup C.qU ∧ ActsAsTensor Q Z C.M₀ C.φ t g o := by
  have H := hcA.hyp
  obtain ⟨g₀, hg₀⟩ := hcA.conj
  have hZne : Z ≠ ⊥ := by
    intro h
    have h4 := H.q4
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have haA : g₀ * (z : G) * g₀⁻¹ ∈ A := by
    rw [hg₀, mem_conjSubgroup]
    simpa [mul_assoc] using z.2
  have ha1 : g₀ * (z : G) * g₀⁻¹ ≠ 1 := by
    intro h
    apply hz1'
    have : (z : G) = g₀⁻¹ * (g₀ * (z : G) * g₀⁻¹) * g₀ := by group
    rw [this, h]; group
  have haQ : g₀ * (z : G) * g₀⁻¹ ∈ Q := hcA.le haA
  have haZ : g₀ * (z : G) * g₀⁻¹ ∉ Z := by
    intro h
    have hm : g₀ * (z : G) * g₀⁻¹ ∈ Z ⊓ A := ⟨h, haA⟩
    rw [hcA.inf_eq_bot, Subgroup.mem_bot] at hm
    exact ha1 hm
  obtain ⟨c₁, c₂, u, hc, hu0, hqu, hpa⟩ :=
    (C.hF.root z z.2 hz1' _ haQ haZ).mp (isConj_iff.mpr ⟨g₀, rfl⟩)
  have hcne : (![c₁, c₂] : Fin 2 → C.K) ≠ 0 := by
    intro h
    rcases hc with hc | hc
    · exact hc (by simpa using congrFun h 0)
    · exact hc (by simpa using congrFun h 1)
  obtain ⟨h, hdet, hh⟩ := exists_change_pure (![c₁, c₂] : Fin 2 → C.K) hcne u
  have hpa' : (C.φ.trans (orthTensorEquiv h)) (C.M₀.π (g₀ * (z : G) * g₀⁻¹)) = (u, 0) := by
    rw [LinearEquiv.trans_apply, hpa, orthTensorEquiv_apply]
    simpa using hh
  have hF' := C.hF.change hdet
  have hAct' := C.hA.change hdet
  obtain ⟨β, o, hiso, hou, hact, hD⟩ :=
    exists_unipotent_act hcA hLA C.hD hAct' hu0 haA ha1 hpa' ht
  have hperp := img_inf_QB_eq_perpLine hcB hcA hno hLA C.hD hF'.toPreFrame hAct' hn hu0 hqu haA
    ha1 hpa'
  have hnd : (QuadraticMap.polarBilin C.qU).Nondegenerate :=
    polarBilin_nondegenerate_of_hnd C.hF.nondeg
  have hoO : o ∈ TauCeti.QuadraticMap.orthogonalGroup C.qU :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have hpr : ∀ v, QuadraticMap.polar C.qU v u = 0 → ∃ c : C.K, o v = v + c • u := by
    intro v hv
    have hmem : (C.φ.trans (orthTensorEquiv h)).symm (v, 0) ∈ C.M₀.img (Q ⊓ QB A) :=
      (hperp _).mpr (by
        rw [LinearEquiv.apply_symm_apply]
        exact ⟨hv, Submodule.zero_mem _⟩)
    obtain ⟨c, hc⟩ := hD _ hmem
    rw [LinearEquiv.apply_symm_apply, orthTensor_unipotent] at hc
    have h1 := congrArg Prod.fst hc
    simp only [Prod.fst_sub, Prod.smul_fst, map_zero, smul_zero, add_zero] at h1
    exact ⟨c, by rw [← h1]; abel⟩
  have hopr : o ∈ pointRad (QuadraticMap.polarBilin C.qU) u := by
    refine ⟨fun x y => ?_, hou, fun v hv => hpr v ?_⟩
    · simp only [QuadraticMap.polarBilin_apply_apply]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hoO x y
    · simpa [QuadraticMap.polarBilin_apply_apply] using hv
  have hoE : o ∈ elementaryGroup C.qU :=
    mem_elementaryGroup_of_mem_pointRad hnd hqu hu0
      (by rw [orthSubgroup_eq_orthogonalGroup]; exact hoO) hopr
  obtain ⟨g', hg', hact'⟩ := actsAsTensor_of_change h hdet
    (g := !![1, β; 0, 1]) (by simp [Matrix.det_fin_two]) hact
  exact ⟨g', o, hg', hoE, hact'⟩

theorem lgen_act_elementary {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (hno : NoA2 Q Z (LB M Q B)) (C : OrthCtx M Q Z B) {s : G} (hs : s ∈ Lgen M (LB M Q B)) :
    ∃ (g : Matrix (Fin 2) (Fin 2) C.K) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)), g.det = 1 ∧
      o ∈ elementaryGroup C.qU ∧ ActsAsTensor Q Z C.M₀ C.φ s g o := by
  have hcB := hc.ctx
  have hn := four_le_card_of_cfg hc C
  let S : Subgroup G :=
    { carrier := {s | s ∈ M ∧ ∃ (g : Matrix (Fin 2) (Fin 2) C.K)
        (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)), g.det = 1 ∧ o ∈ elementaryGroup C.qU ∧
          ActsAsTensor Q Z C.M₀ C.φ s g o}
      mul_mem' := by
        rintro a b ⟨haM, g₁, o₁, hg₁, ho₁, hact₁⟩ ⟨hbM, g₂, o₂, hg₂, ho₂, hact₂⟩
        refine ⟨M.mul_mem haM hbM, g₁ * g₂, o₁ * o₂, by rw [Matrix.det_mul, hg₁, hg₂, one_mul],
          Subgroup.mul_mem _ ho₁ ho₂, ?_⟩
        exact ActsAsTensor.mul (o := (o₁ : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)))
          (o' := (o₂ : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)))
          (hcB.conj_mem_Q_of_mem_M hbM).1 hact₁ hact₂
      one_mem' := ⟨M.one_mem, 1, 1, by simp, Subgroup.one_mem _, ActsAsTensor.of_mem Q.one_mem⟩
      inv_mem' := by
        rintro a ⟨haM, g, o, hg, ho, hact⟩
        have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (by rw [hg]; exact isUnit_one)
        have h2 : g⁻¹.det = 1 := by
          have := congrArg Matrix.det h1
          rwa [Matrix.det_mul, hg, one_mul, Matrix.det_one] at this
        exact ⟨M.inv_mem haM, g⁻¹, o.symm, h2, Subgroup.inv_mem _ ho,
          ActsAsTensor.inv (hcB.conj_mem_Q_of_mem_M haM).2 hact h1⟩ }
  have hLS : Lgen M (LB M Q B) ≤ S := by
    refine iSup₂_le fun m hm t ht => ?_
    have hcA := hcB.conj_of_mem hm
    have hLA : LB M Q (conjSubgroup m B) ≤ Lgen M (LB M Q B) := by
      rw [hcB.LB_conj hm]
      exact le_iSup₂_of_le m hm le_rfl
    have ht' : t ∈ LB M Q (conjSubgroup m B) := by rwa [hcB.LB_conj hm]
    obtain ⟨g, o, hg, ho, hact⟩ :=
      lA_act_elementary hcB hcA (hcB.noA2_conj hno hm) hLA C hn ht'
    exact ⟨hcA.LB_le_M ht', g, o, hg, ho, hact⟩
  obtain ⟨-, g, o, hg, ho, hact⟩ := hLS hs
  exact ⟨g, o, hg, ho, hact⟩

theorem lgen_act_omega {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (hno : NoA2 Q Z (LB M Q B)) (C : OrthCtx M Q Z B) {s : G} (hs : s ∈ Lgen M (LB M Q B)) :
    ∃ (g : Matrix (Fin 2) (Fin 2) C.K) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)), g.det = 1 ∧
      o ∈ OrthogonalInvolutions.omegaGroup C.qU (polarBilin_nondegenerate_of_hnd C.hF.nondeg) ∧
        ActsAsTensor Q Z C.M₀ C.φ s g o := by
  obtain ⟨g, o, hg, ho, hact⟩ := lgen_act_elementary hc hno C hs
  exact ⟨g, o, hg, CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup _ ho, hact⟩

theorem lgen_act_even {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (hno : NoA2 Q Z (LB M Q B)) (C : OrthCtx M Q Z B) {s : G} (hs : s ∈ Lgen M (LB M Q B)) :
    ∃ (g : Matrix (Fin 2) (Fin 2) C.K) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)), g.det = 1 ∧
      (∀ v, C.qU (o v) = C.qU v) ∧
        Even (Module.finrank C.K (OrthogonalInvolutions.commSpace o)) ∧
        ActsAsTensor Q Z C.M₀ C.φ s g o := by
  obtain ⟨g, o, hg, ho, hact⟩ := lgen_act_omega hc hno C hs
  exact ⟨g, o, hg, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp ho.1, ho.2, hact⟩

theorem inv_mul_mem_Q_of_same_act {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) (C : OrthCtx M Q Z B)
    {w s : G} (hw : w ∈ M) (hs : s ∈ M) {g g' : Matrix (Fin 2) (Fin 2) C.K}
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hgg' : g' * g = 1)
    (hwa : ActsAsTensor Q Z C.M₀ C.φ w g o) (hsa : ActsAsTensor Q Z C.M₀ C.φ s g o) :
    s⁻¹ * w ∈ Q := by
  refine mem_Q_of_pi_conj_eq (M₀ := C.M₀) hc.hyp (M.mul_mem (M.inv_mem hs) hw) fun x hx => ?_
  have hyQ : w * x * w⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hw).1 x hx
  have hy'Q : s⁻¹ * (w * x * w⁻¹) * s ∈ Q := (hc.conj_mem_Q_of_mem_M hs).2 _ hyQ
  have e1 := hsa _ hy'Q
  have e2 : s * (s⁻¹ * (w * x * w⁻¹) * s) * s⁻¹ = w * x * w⁻¹ := by group
  rw [e2, hwa x hx] at e1
  have e3 := congrArg (orthTensor g' o.symm) e1
  rw [orthTensor_symm_comp g g' o hgg', orthTensor_symm_comp g g' o hgg'] at e3
  have e4 : (s⁻¹ * w) * x * (s⁻¹ * w)⁻¹ = s⁻¹ * (w * x * w⁻¹) * s := by group
  rw [e4]
  exact (C.φ.injective e3).symm

theorem mem_Lgen_of_act_elementary {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) {w : G} (hw : w ∈ M) {g : Matrix (Fin 2) (Fin 2) C.K}
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hg : g.det = 1) (ho : o ∈ elementaryGroup C.qU)
    (hact : ActsAsTensor Q Z C.M₀ C.φ w g o) : w ∈ Lgen M (LB M Q B) := by
  have hcB := hc.ctx
  have hS : ∀ s ∈ Lgen M (LB M Q B), ∀ x ∈ Q, s * x * s⁻¹ ∈ Q := fun s hs x hx =>
    (hcB.conj_mem_Q_of_mem_M (Lgen_le hcB.LB_le_M hs)).1 x hx
  obtain ⟨s₁, hs₁, hact₁⟩ := exists_lgen_actsAs_elementary C.hA hS ho
  obtain ⟨s₂, hs₂, hact₂⟩ := C.hA.sl g hg
  have hs₂₁ : s₂ * s₁ ∈ Lgen M (LB M Q B) := Subgroup.mul_mem _ hs₂ hs₁
  have hact₃ : ActsAsTensor Q Z C.M₀ C.φ (s₂ * s₁) g o := by
    have := ActsAsTensor.mul (o := LinearMap.id)
      (o' := (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K))) (hS s₁ hs₁) hact₂ hact₁
    rw [mul_one] at this
    exact this
  have hg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (by rw [hg]; exact isUnit_one)
  have hmemQ := inv_mul_mem_Q_of_same_act hcB C hw (Lgen_le hcB.LB_le_M hs₂₁) hg' hact hact₃
  have hw' : w = (s₂ * s₁) * ((s₂ * s₁)⁻¹ * w) := by group
  rw [hw']
  exact Subgroup.mul_mem _ hs₂₁
    ((le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M)).trans (le_Lgen_self M (LB M Q B)) hmemQ)

end LgenAct

section Normalized

open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

variable [Finite G]

private theorem eq_one_of_sq_eq_one' {K : Type} [Field K] [CharP K 2] {a : K} (h : a ^ 2 = 1) :
    a = 1 := by
  have h' : a ^ 2 = 1 ^ 2 := by rw [h, one_pow]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h' with h1 | h1
  · exact h1
  · rwa [CharTwo.neg_eq] at h1

theorem exists_map_ne_zero_of_ctx {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) (C : OrthCtx M Q Z B) :
    ∃ v : C.ι → C.K, C.qU v ≠ 0 := by
  obtain ⟨u, hu0, hqu⟩ := exists_singular_of_ctx hc C
  obtain ⟨w, hw⟩ : ∃ w, QuadraticMap.polar C.qU u w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (C.hF.nondeg u h)
  by_cases hw0 : C.qU w = 0
  · refine ⟨u + w, fun h => hw ?_⟩
    have := QuadraticMap.map_add C.qU u w
    rw [h, hqu, hw0] at this
    simpa using this.symm
  · exact ⟨w, hw0⟩

theorem exists_normalized_involution_of_sim {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) (hsim : OrthSim C) {w : G} (hw : w ∈ H0 M Z) (hw2 : w * w = 1) :
    ∃ (g : Matrix (Fin 2) (Fin 2) C.K) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)),
      ActsAsTensor Q Z C.M₀ C.φ w g o ∧ g * g = 1 ∧ (∀ v, o (o v) = v) ∧
        ∀ v, C.qU (o v) = C.qU v := by
  classical
  obtain ⟨g, o, ρ, hg, hρ, hq, hact⟩ := hsim w hw
  have hsQ := (hc.ctx.conj_mem_Q_of_mem_M hw.1).1
  obtain ⟨u, hu0, -⟩ := exists_singular_of_ctx hc.ctx C
  haveI : Nonempty C.ι := by
    by_contra h
    exact hu0 (funext fun i => (h ⟨i⟩).elim)
  set ℓ : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K) := (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K))
  have hsq := ActsAsTensor.mul (M₀ := C.M₀) (φ := C.φ) (o := ℓ) (o' := ℓ) hsQ hact hact
  rw [hw2] at hsq
  have hfix : ∀ p, orthTensor (g * g) (ℓ ∘ₗ ℓ) p = p := by
    intro p
    obtain ⟨x, hx, rfl⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) p
    have hx' := hsq x hx
    simp only [one_mul, inv_one, mul_one] at hx'
    exact hx'.symm
  obtain ⟨κ, hκ0, hκg, hκo⟩ := exists_scalar_of_orthTensor_eq_self (g * g) (ℓ ∘ₗ ℓ) hfix
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq C.K 2) κ
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hκ0
    rw [hμ, h0, mul_zero]
  have key : ∀ (c : C.K) (v : C.ι → C.K), (μ⁻¹ * c) • (μ • v) = c • v := by
    intro c v
    rw [smul_smul, mul_right_comm, inv_mul_cancel₀ hμ0, one_mul]
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero_of_ctx hc.ctx C
  have hκρ : κ * ρ = 1 := by
    have h1 : C.qU v₀ = (κ * ρ) ^ 2 * C.qU v₀ := by
      have h2 := hκo v₀
      calc C.qU v₀ = C.qU (κ • (ℓ ∘ₗ ℓ) v₀) := by rw [h2]
        _ = (κ * ρ) ^ 2 * C.qU v₀ := by
          rw [QuadraticMap.map_smul]
          simp only [LinearMap.comp_apply, smul_eq_mul]
          show κ * κ * C.qU (o (o v₀)) = _
          rw [hq, hq]
          ring
    have h3 : ((κ * ρ) ^ 2 - 1) * C.qU v₀ = 0 := by linear_combination -h1
    have h4 := (mul_eq_zero.mp h3).resolve_right hv₀
    exact eq_one_of_sq_eq_one' (sub_eq_zero.mp h4)
  refine ⟨μ⁻¹ • g, o.trans (LinearEquiv.smulOfNeZero C.K (C.ι → C.K) μ hμ0), ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hact x hx]
    simp [orthTensor, smul_eq_mul, key]
  · have hc' : μ⁻¹ * μ⁻¹ * κ = 1 := by
      rw [hμ]
      field_simp
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hκg, smul_smul, hc', one_smul]
  · intro v
    have hv := hκo v
    rw [LinearMap.comp_apply] at hv
    simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, map_smul]
    rw [smul_smul, ← hμ]
    exact hv
  · intro v
    simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, QuadraticMap.map_smul,
      smul_eq_mul, hq]
    calc μ * μ * (ρ * C.qU v) = (κ * ρ) * C.qU v := by rw [hμ]; ring
      _ = C.qU v := by rw [hκρ, one_mul]

theorem orthNormalized_mul {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) (C : OrthCtx M Q Z B)
    {w₁ w₂ : G} (hw₂ : w₂ ∈ M) {g₁ g₂ g₃ : Matrix (Fin 2) (Fin 2) C.K}
    {o₁ o₂ o₃ : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (h1 : ActsAsTensor Q Z C.M₀ C.φ w₁ g₁ o₁) (h2 : ActsAsTensor Q Z C.M₀ C.φ w₂ g₂ o₂)
    (h3 : ActsAsTensor Q Z C.M₀ C.φ (w₁ * w₂) g₃ o₃) (hg3 : g₃ * g₃ = 1)
    (ho3 : ∀ v, o₃ (o₃ v) = v) (iso₁ : ∀ v, C.qU (o₁ v) = C.qU v)
    (iso₂ : ∀ v, C.qU (o₂ v) = C.qU v) (iso₃ : ∀ v, C.qU (o₃ v) = C.qU v) : o₃ = o₁ * o₂ := by
  classical
  obtain ⟨u, hu0, -⟩ := exists_singular_of_ctx hc C
  haveI : Nonempty C.ι := by
    by_contra h
    exact hu0 (funext fun i => (h ⟨i⟩).elim)
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero_of_ctx hc C
  have hmul := ActsAsTensor.mul (M₀ := C.M₀) (φ := C.φ) (o := (o₁ : (C.ι → C.K) →ₗ[C.K] _))
    (o' := (o₂ : (C.ι → C.K) →ₗ[C.K] _)) (hc.conj_mem_Q_of_mem_M hw₂).1 h1 h2
  have heq := hmul.orthTensor_eq h3
  have hfix : ∀ p, orthTensor (g₃ * (g₁ * g₂)) ((o₃ : (C.ι → C.K) →ₗ[C.K] _) ∘ₗ
      ((o₁ : (C.ι → C.K) →ₗ[C.K] _) ∘ₗ (o₂ : (C.ι → C.K) →ₗ[C.K] _))) p = p := by
    intro p
    calc orthTensor (g₃ * (g₁ * g₂)) ((o₃ : (C.ι → C.K) →ₗ[C.K] _) ∘ₗ
          ((o₁ : (C.ι → C.K) →ₗ[C.K] _) ∘ₗ (o₂ : (C.ι → C.K) →ₗ[C.K] _))) p
        = orthTensor g₃ (⇑o₃) (orthTensor (g₁ * g₂) (⇑((o₁ : (C.ι → C.K) →ₗ[C.K] _) ∘ₗ
            (o₂ : (C.ι → C.K) →ₗ[C.K] _))) p) :=
          (orthTensor_comp g₃ (g₁ * g₂) (o₃ : (C.ι → C.K) →ₗ[C.K] _)
            ((o₁ : (C.ι → C.K) →ₗ[C.K] _) ∘ₗ (o₂ : (C.ι → C.K) →ₗ[C.K] _)) p).symm
      _ = orthTensor g₃ (⇑o₃) (orthTensor g₃ (⇑o₃) p) := by rw [heq p]
      _ = orthTensor (g₃ * g₃) ((o₃ : (C.ι → C.K) →ₗ[C.K] _) ∘ₗ (o₃ : (C.ι → C.K) →ₗ[C.K] _)) p :=
          orthTensor_comp g₃ g₃ (o₃ : (C.ι → C.K) →ₗ[C.K] _) (o₃ : (C.ι → C.K) →ₗ[C.K] _) p
      _ = p := by
          rw [hg3, orthTensor_one_linear]
          exact Prod.ext (ho3 _) (ho3 _)
  obtain ⟨κ, hκ0, -, hκo⟩ := exists_scalar_of_orthTensor_eq_self _ _ hfix
  have hκ : κ = 1 := by
    have h1' : C.qU v₀ = κ ^ 2 * C.qU v₀ := by
      have h2' := hκo v₀
      calc C.qU v₀ = C.qU (κ • (o₃ (o₁ (o₂ v₀)))) := congrArg C.qU h2'.symm
        _ = κ ^ 2 * C.qU v₀ := by
          rw [QuadraticMap.map_smul, iso₃, iso₁, iso₂, smul_eq_mul]; ring
    have h3' : (κ ^ 2 - 1) * C.qU v₀ = 0 := by linear_combination -h1'
    exact eq_one_of_sq_eq_one' (sub_eq_zero.mp ((mul_eq_zero.mp h3').resolve_right hv₀))
  refine LinearEquiv.ext fun v => ?_
  have h4 := hκo (v := v)
  rw [hκ, one_smul] at h4
  have h5 : o₃ (o₃ (o₁ (o₂ v))) = o₃ v := by
    have : o₃ (o₁ (o₂ v)) = v := h4
    rw [this]
  rw [ho3] at h5
  exact h5.symm

end Normalized

section R0

variable [Finite G]

theorem mem_Lgen_of_normalized_even {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) {w : G} (hw : w ∈ M) {g : Matrix (Fin 2) (Fin 2) C.K}
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hgg : g * g = 1) (hiso : ∀ v, C.qU (o v) = C.qU v)
    (heven : Even (Module.finrank C.K (OrthogonalInvolutions.commSpace o)))
    (hact : ActsAsTensor Q Z C.M₀ C.φ w g o) : w ∈ Lgen M (LB M Q B) := by
  have hdet : g.det = 1 := by
    have h := congrArg Matrix.det hgg
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact eq_one_of_sq_eq_one' (by rw [pow_two]; exact h)
  have ho : o ∈ OrthogonalInvolutions.omegaGroup C.qU
      (polarBilin_nondegenerate_of_hnd C.hF.nondeg) :=
    ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso, heven⟩
  exact mem_Lgen_of_act_elementary hc C hw hdet (omegaGroup_le_elementaryGroup_of_cfg hc C ho) hact

theorem orthR0_of_sim {M Q Z B X : Subgroup G} {x : G} (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) (hsim : OrthSim C) (hs : Sit M Q Z X x) :
    ∃ x₀ ∈ X, x₀ ≠ 1 ∧ x₀ ∈ Lgen M (LB M Q B) := by
  have hcB := hc.ctx
  have H := hcB.hyp
  have hXH : X ≤ H0 M Z := (smith_1_12 hs).1
  have hX2 : ∀ w ∈ X, w * w = 1 := by
    intro w hw
    obtain ⟨g, hg⟩ := hs.conj
    have hw' : g⁻¹ * w * g ∈ Z := mem_conjSubgroup.mp (hg ▸ hw)
    have h1 := Z_sq H hw'
    have e : w * w = g * ((g⁻¹ * w * g) ^ 2) * g⁻¹ := by rw [pow_two]; group
    rw [e, h1]; group
  have hXcard : 4 ≤ Nat.card X := by
    obtain ⟨g, hg⟩ := hs.conj
    rw [hg, card_conjSubgroup]
    exact H.q4
  obtain ⟨y, hyX, hy1, hyx⟩ : ∃ y ∈ X, y ≠ 1 ∧ y ≠ x := by
    by_contra hcon
    push Not at hcon
    have hsub : (X : Set G) ⊆ {1, x} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (hcon y hy h1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, x} : Set G).ncard ≤ 2 := (Set.ncard_insert_le 1 {x}).trans (by simp)
    have h3 : Nat.card X = (X : Set G).ncard := Nat.card_coe_set_eq (X : Set G)
    omega
  have hxyX : x * y ∈ X := X.mul_mem hs.mem hyX
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hyx
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_eq_of_mul_eq_one_right hs.x_sq
  obtain ⟨g₁, o₁, a₁, gg₁, oo₁, iso₁⟩ :=
    exists_normalized_involution_of_sim hc C hsim (hXH hs.mem) hs.x_sq
  obtain ⟨g₂, o₂, a₂, gg₂, oo₂, iso₂⟩ :=
    exists_normalized_involution_of_sim hc C hsim (hXH hyX) (hX2 y hyX)
  obtain ⟨g₃, o₃, a₃, gg₃, oo₃, iso₃⟩ :=
    exists_normalized_involution_of_sim hc C hsim (hXH hxyX) (hX2 _ hxyX)
  have hprod : o₃ = o₁ * o₂ := orthNormalized_mul hcB C (hXH hyX).1 a₁ a₂ a₃ gg₃ oo₃ iso₁ iso₂ iso₃
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  have hD := OrthogonalInvolutions.natCast_finrank_commSpace_mul hnd
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr iso₁)
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr iso₂)
  rw [← hprod] at hD
  have key : ∀ a b c : ZMod 2, c = a + b → a = 0 ∨ b = 0 ∨ c = 0 := by decide
  rcases key _ _ _ hD with h | h | h
  · exact ⟨x, hs.mem, hs.ne_one, mem_Lgen_of_normalized_even hc C hs.memM gg₁ iso₁
      (ZMod.natCast_eq_zero_iff_even.mp h) a₁⟩
  · exact ⟨y, hyX, hy1, mem_Lgen_of_normalized_even hc C (hXH hyX).1 gg₂ iso₂
      (ZMod.natCast_eq_zero_iff_even.mp h) a₂⟩
  · exact ⟨x * y, hxyX, hxy1, mem_Lgen_of_normalized_even hc C (hXH hxyX).1 gg₃ iso₃
      (ZMod.natCast_eq_zero_iff_even.mp h) a₃⟩

@[expose] def OrthR0HypFourStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ C : OrthCtx M Q Z B, Fintype.card C.ι = 4 → ¬ NoTotallySingularPlane C.qU →
      ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
        ∃ x₀ ∈ X, x₀ ≠ 1 ∧ x₀ ∈ Lgen M (LB M Q B)

theorem orthR0_of_hypFour (h24 : Smith24ActStatement) (h : OrthR0HypFourStatement) :
    OrthR0Statement := by
  intro G _ _ M Q Z B hc X x hs
  obtain ⟨C⟩ := exists_orthCtx h24 hc
  by_cases hdim : Fintype.card C.ι ≠ 4 ∨ NoTotallySingularPlane C.qU
  · exact orthR0_of_sim hc C (orthSim_of_dim hc C hdim) hs
  · push Not at hdim
    exact h G M Q Z B hc C hdim.1 hdim.2 X x hs

theorem orthNormalized_unique {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) (C : OrthCtx M Q Z B)
    {w : G} {g g' : Matrix (Fin 2) (Fin 2) C.K} {o o' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (h : ActsAsTensor Q Z C.M₀ C.φ w g o) (h' : ActsAsTensor Q Z C.M₀ C.φ w g' o')
    (hg' : g' * g' = 1) (ho' : ∀ v, o' (o' v) = v) (iso : ∀ v, C.qU (o v) = C.qU v)
    (iso' : ∀ v, C.qU (o' v) = C.qU v) : o' = o := by
  have h1 : ActsAsTensor Q Z C.M₀ C.φ (1 : G) 1 (1 : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)) :=
    ActsAsTensor.of_mem Q.one_mem
  have := orthNormalized_mul hc C (w₁ := w) (w₂ := 1) (g₁ := g) (g₂ := 1) (g₃ := g')
    (o₁ := o) (o₂ := 1) (o₃ := o') M.one_mem h h1 (by rwa [mul_one])
    hg' ho' iso (fun v => rfl) iso'
  simpa using this

theorem lgen_involution_normalized {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (hno : NoA2 Q Z (LB M Q B)) (C : OrthCtx M Q Z B) {w : G} (hw : w ∈ Lgen M (LB M Q B))
    (hw2 : w * w = 1) :
    ∃ (g : Matrix (Fin 2) (Fin 2) C.K) (o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)),
      ActsAsTensor Q Z C.M₀ C.φ w g o ∧ g * g = 1 ∧ (∀ v, o (o v) = v) ∧
        (∀ v, C.qU (o v) = C.qU v) ∧
          Even (Module.finrank C.K (OrthogonalInvolutions.commSpace o)) := by
  classical
  obtain ⟨g, o, hg, hiso, heven, hact⟩ := lgen_act_even hc hno C hw
  obtain ⟨u, hu0, -⟩ := exists_singular_of_ctx hc.ctx C
  haveI : Nonempty C.ι := by
    by_contra h
    exact hu0 (funext fun i => (h ⟨i⟩).elim)
  have hwM : w ∈ M := Lgen_le hc.ctx.LB_le_M hw
  set ℓ : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K) := (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K))
  have hsq := ActsAsTensor.mul (M₀ := C.M₀) (φ := C.φ) (o := ℓ) (o' := ℓ)
    (hc.ctx.conj_mem_Q_of_mem_M hwM).1 hact hact
  rw [hw2] at hsq
  have hfix : ∀ p, orthTensor (g * g) (ℓ ∘ₗ ℓ) p = p := by
    intro p
    obtain ⟨x, hx, rfl⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) p
    have hx' := hsq x hx
    simp only [one_mul, inv_one, mul_one] at hx'
    exact hx'.symm
  obtain ⟨κ, -, hκg, hκo⟩ := exists_scalar_of_orthTensor_eq_self (g * g) (ℓ ∘ₗ ℓ) hfix
  have h1 : κ ^ 2 = 1 := by
    have := congrArg Matrix.det hκg
    rw [Matrix.det_mul, hg, mul_one, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at this
    exact this.symm
  have hκ : κ = 1 := eq_one_of_sq_eq_one' h1
  refine ⟨g, o, hact, by rw [hκg, hκ, one_smul], fun v => ?_, hiso, heven⟩
  have := hκo v
  rwa [hκ, one_smul] at this

theorem mem_Lgen_iff_normalized_even {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (hno : NoA2 Q Z (LB M Q B)) (C : OrthCtx M Q Z B)
    {w : G} (hw : w ∈ M) (hw2 : w * w = 1)
    {g : Matrix (Fin 2) (Fin 2) C.K} {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hgg : g * g = 1)
    (hoo : ∀ v, o (o v) = v) (hiso : ∀ v, C.qU (o v) = C.qU v)
    (hact : ActsAsTensor Q Z C.M₀ C.φ w g o) :
    w ∈ Lgen M (LB M Q B) ↔ Even (Module.finrank C.K (OrthogonalInvolutions.commSpace o)) := by
  constructor
  · intro hwL
    obtain ⟨g', o', hact', hgg', hoo', hiso', heven'⟩ := lgen_involution_normalized hc hno C hwL hw2
    have := orthNormalized_unique hc.ctx C hact hact' hgg' hoo' hiso hiso'
    rwa [this] at heven'
  · exact fun h => mem_Lgen_of_normalized_even hc C hw hgg hiso h hact

theorem noA2_of_tacit (hT : OrthTacitStatement) {M Q Z B : Subgroup G}
    (hc : SmithOrthCfg M Q Z B) : NoA2 Q Z (LB M Q B) :=
  (hT G M Q Z B hc B hc.ctx).1

end R0

end CFSG.RankThree.GF2n.Smith81
