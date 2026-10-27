module

public import CFSG.Monster.B.Cbar.TraceIdentity
public import CFSG.Monster.B.Cbar.FourGroupSpin
public import CFSG.Monster.Triality

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Parity CFSG.Monster.Generated
  CFSG.Monster.VisCert CFSG.Monster.ScalarKernel

@[expose] def involQmat : Set (SpaceB ≃ₗ[ℚ] SpaceB) := {g | g ∈ Qmat ∧ g ≠ 1 ∧ g * g = 1}

@[expose] def shortInv : Set (SpaceB ≃ₗ[ℚ] SpaceB) :=
  rhoEquiv '' {r : Q | IsShortCoord (coordOf r)}

@[expose] def frameInv : Set (SpaceB ≃ₗ[ℚ] SpaceB) :=
  rhoEquiv '' {r : Q | Multiplicative.toAdd (phi (QuotientGroup.mk r)) ∈ frameDelta}

private theorem rho_one : rhoEquiv 1 = 1 :=
  (congrArg thetaEquiv (map_one rhoPair)).trans thetaEquiv_one

private theorem rho_eq_one_iff {r : Q} : rhoEquiv r = 1 ↔ r = 1 :=
  ⟨fun h => rhoEquiv_injective (h.trans rho_one.symm), fun h => h ▸ rho_one⟩

private theorem rho_mul_self (r : Q) : rhoEquiv r * rhoEquiv r = rhoEquiv (r * r) :=
  (rhoEquiv_mul r r).symm

theorem mul_self_eq_one_iff_qL (r : Q) : r * r = 1 ↔ qL (phi0 (coordOf r)) = 0 := by
  rw [qL_phi0]
  have hx : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  have hsq := SpinCoord.sq_eq (spinEquiv.symm r)
  constructor
  · intro h
    have h2 : spinEquiv.symm r ^ 2 = 1 := by
      rw [pow_two, ← map_mul, h, map_one]
    rw [hsq] at h2
    exact congrArg SpinCoord.s h2
  · intro h
    have h2 : spinEquiv.symm r ^ 2 = 1 := by
      rw [hsq]
      exact SpinCoord.ext h rfl rfl
    calc r * r = spinEquiv (spinEquiv.symm r ^ 2) := by rw [map_pow, hx, pow_two]
      _ = 1 := by rw [h2, map_one]

theorem coordOf_one : coordOf (1 : Q) = 0 := by
  rw [coordOf, map_one]
  rfl

theorem coordOf_zQ : coordOf zQ = 0 := by
  rw [coordOf, zQ, MulEquiv.symm_apply_apply]
  rfl

theorem eq_one_or_zQ_of_coordOf_eq_zero {r : Q} (h : coordOf r = 0) : r = 1 ∨ r = zQ := by
  rcases Short.eq_or_eq_zQ_mul_of_coordOf_eq (h.trans coordOf_one.symm) with h1 | h1
  · exact .inl h1
  · exact .inr (h1.trans (mul_one zQ))

theorem toAdd_phi_eq (r : Q) :
    Multiplicative.toAdd (phi (QuotientGroup.mk r)) = phi0 (coordOf r) := toAdd_phi_mk r

theorem mem_frameDelta_phi_iff (r : Q) :
    Multiplicative.toAdd (phi (QuotientGroup.mk r)) ∈ frameDelta ↔ phi0 (coordOf r) ∈ frameDelta :=
  iff_of_eq (congrArg (· ∈ frameDelta) (toAdd_phi_eq r))

theorem not_mem_center_of_phi0_ne_zero {s : Q} (hs : phi0 (coordOf s) ≠ 0) :
    s ∉ Subgroup.center Q := by
  intro hc
  rw [center_Q] at hc
  rcases (mem_zpowers_iff_of_orderOf_eq_two orderOf_zQ).1 hc with h | h
  · apply hs
    rw [h, coordOf_one, map_zero]
  · apply hs
    rw [h, coordOf_zQ, map_zero]

theorem exists_conjQ_eq_of_noncentral {r s : Q} (hs : s ∉ Subgroup.center Q) (p : Pvis)
    (h : modTwoEnd p.1.2 (phi0 (coordOf r)) = phi0 (coordOf s)) :
    ∃ p' : Pvis, conjQ p' r = s := by
  have hcl : phi0 (coordOf (conjQ p r)) = phi0 (coordOf s) :=
    (toAdd_phi_mk (conjQ p r)).symm.trans ((phi_conjQ p r).trans
      ((congrArg (modTwoEnd p.1.2) (toAdd_phi_mk r)).trans h))
  rcases Short.eq_or_eq_zQ_mul_of_coordOf_eq (phi0_injective hcl) with h1 | h1
  · exact ⟨p, h1⟩
  · obtain ⟨q, hq⟩ := Short.exists_conj_eq_zQ_mul hs
    refine ⟨p * rhoPair q, ?_⟩
    exact (conjQ_mul p (rhoPair q) r).trans ((congrArg (conjQ (rhoPair q)) h1).trans
      ((conjQ_rhoPair q (zQ * s)).trans
        (Short.conj_mul_eq_of_conj Short.zQ_mem_center Short.zQ_mul_zQ hq)))

theorem xmat_mem_involQmat : xmat ∈ involQmat := by
  refine ⟨xmat_mem_Qmat, generated_rational_group_finite_centralizer.2.2.2.2.2.2.2.1, ?_⟩
  rw [xmat_eq_xB]
  exact xB_mul_self

theorem rho_mem_involQmat_iff (r : Q) :
    rhoEquiv r ∈ involQmat ↔ r ≠ 1 ∧ qL (phi0 (coordOf r)) = 0 := by
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨fun h => h1 (rho_eq_one_iff.2 h), (mul_self_eq_one_iff_qL r).1 ?_⟩
    rw [rho_mul_self] at h2
    exact rho_eq_one_iff.1 h2
  · rintro ⟨h1, h2⟩
    refine ⟨rhoEquiv_mem_rhoQ r, fun h => h1 (rho_eq_one_iff.1 h), ?_⟩
    rw [rho_mul_self, (mul_self_eq_one_iff_qL r).2 h2, rho_one]

theorem shortInv_subset : shortInv ⊆ involQmat := by
  rintro _ ⟨r, hr, rfl⟩
  have hr' : IsShortCoord (coordOf r) := hr
  refine (rho_mem_involQmat_iff r).2 ⟨fun h => ?_, ?_⟩
  · subst h
    rw [coordOf_one] at hr'
    exact not_isShortCoord_zero hr'
  · obtain ⟨u, hu, hcl⟩ := hr'
    rw [← hcl]
    exact qL_classOf_minVecs hu

theorem frameInv_subset : frameInv ⊆ involQmat := by
  rintro _ ⟨r, hr0, rfl⟩
  have hr := (mem_frameDelta_phi_iff r).1 hr0
  refine (rho_mem_involQmat_iff r).2 ⟨fun h => ?_, hr.2.1⟩
  apply hr.1
  rw [h, coordOf_one, map_zero]

theorem involQmat_eq : involQmat = {xmat} ∪ shortInv ∪ frameInv := by
  ext g
  constructor
  · intro hg
    obtain ⟨r, rfl⟩ := mem_rhoQ.1 hg.1
    obtain ⟨hr1, hq⟩ := (rho_mem_involQmat_iff r).1 hg
    by_cases h0 : phi0 (coordOf r) = 0
    · rcases eq_one_or_zQ_of_coordOf_eq_zero (phi0_injective (h0.trans (map_zero phi0).symm))
        with h | h
      · exact absurd h hr1
      · left; left
        rw [h]
        rfl
    · by_cases hs : IsShortCoord (coordOf r)
      · exact .inl (.inr ⟨r, hs, rfl⟩)
      · exact .inr ⟨r, (mem_frameDelta_phi_iff r).2 ⟨h0, hq, hs⟩, rfl⟩
  · rintro ((h | h) | h)
    · rw [Set.mem_singleton_iff.1 h]
      exact xmat_mem_involQmat
    · exact shortInv_subset h
    · exact frameInv_subset h

theorem xmat_not_mem_shortInv : xmat ∉ shortInv := by
  rintro ⟨r, hr, h⟩
  have hr' : IsShortCoord (coordOf r) := hr
  have hrz : r = zQ := rhoEquiv_injective (h.trans rfl)
  rw [hrz, coordOf_zQ] at hr'
  exact not_isShortCoord_zero hr'

theorem xmat_not_mem_frameInv : xmat ∉ frameInv := by
  rintro ⟨r, hr0, h⟩
  have hr := (mem_frameDelta_phi_iff r).1 hr0
  have hrz : r = zQ := rhoEquiv_injective (h.trans rfl)
  rw [hrz, coordOf_zQ, map_zero] at hr
  exact hr.1 rfl

theorem disjoint_shortInv_frameInv : Disjoint shortInv frameInv := by
  rw [Set.disjoint_left]
  rintro _ ⟨r, hr, rfl⟩ ⟨r', hr0', h⟩
  have hr' := (mem_frameDelta_phi_iff r').1 hr0'
  have hrr : r' = r := rhoEquiv_injective h
  rw [hrr] at hr'
  exact hr'.2.2 hr

theorem Gvis_conj_rho {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) (r : Q) :
    ∃ p : Pvis, g * rhoEquiv r * g⁻¹ = rhoEquiv (conjQ p r) ∧ thetaEquiv p = g := by
  obtain ⟨p, rfl⟩ := mem_Gvis.1 hg
  exact ⟨p, Short.thetaEquiv_conj_rhoEquiv p r, rfl⟩

theorem Gvis_conj_xmat {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) : g * xmat * g⁻¹ = xmat := by
  obtain ⟨p, hp, -⟩ := Gvis_conj_rho hg zQ
  rw [show xmat = rhoEquiv zQ from rfl, hp, conjQ_zQ]

theorem Gvis_conj_mem_shortInv {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) {t : SpaceB ≃ₗ[ℚ] SpaceB}
    (ht : t ∈ shortInv) : g * t * g⁻¹ ∈ shortInv := by
  obtain ⟨r, hr, rfl⟩ := ht
  obtain ⟨p, hp, -⟩ := Gvis_conj_rho hg r
  rw [hp]
  exact ⟨conjQ p r, isShortCoord_conjQ p hr, rfl⟩

theorem Gvis_conj_mem_frameInv {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) {t : SpaceB ≃ₗ[ℚ] SpaceB}
    (ht : t ∈ frameInv) : g * t * g⁻¹ ∈ frameInv := by
  obtain ⟨r, hr, rfl⟩ := ht
  obtain ⟨p, hp, -⟩ := Gvis_conj_rho hg r
  rw [hp]
  refine ⟨conjQ p r, ?_, rfl⟩
  rw [Set.mem_ofPred_eq, phi_conjQ]
  exact (modTwoEnd_mem_frameDelta_iff p.1.2).2 hr

theorem shortInv_transitive
    {s t : SpaceB ≃ₗ[ℚ] SpaceB} (hs : s ∈ shortInv) (ht : t ∈ shortInv) :
    ∃ g ∈ Gvis, g * s * g⁻¹ = t := by
  obtain ⟨r, hr, rfl⟩ := hs
  obtain ⟨r', hr', rfl⟩ := ht
  obtain ⟨g, hg, h, -⟩ := Short.short_label_visible_transitivity.2.2.2.1 r r' hr hr'
  exact ⟨g, hg, h⟩

theorem frameInv_transitive
    {s t : SpaceB ≃ₗ[ℚ] SpaceB} (hs : s ∈ frameInv) (ht : t ∈ frameInv) :
    ∃ g ∈ Gvis, g * s * g⁻¹ = t := by
  obtain ⟨r, hr0, rfl⟩ := hs
  obtain ⟨r', hr0', rfl⟩ := ht
  have hr := (mem_frameDelta_phi_iff r).1 hr0
  have hr' := (mem_frameDelta_phi_iff r').1 hr0'
  obtain ⟨k, hk, hkx⟩ := exists_Kvis_smul_eq hr hr'
  obtain ⟨g, hgP, rfl⟩ := mem_Hvis.1 (Kvis_le_Hvis hk)
  obtain ⟨s', hs'⟩ := mem_PvisLat.1 hgP
  obtain ⟨p', hp'⟩ := exists_conjQ_eq_of_noncentral (not_mem_center_of_phi0_ne_zero hr'.1)
    ⟨(s', g), hs'⟩ hkx
  exact ⟨thetaEquiv p', thetaEquiv_mem_Gvis p', by rw [Short.thetaEquiv_conj_rhoEquiv, hp']⟩

noncomputable def shortLiftEquiv : {r : Q | IsShortCoord (coordOf r)} ≃ ZMod 2 × ShortIdx where
  toFun r := (centralCoord r.1, ⟨coordOf r.1, r.2⟩)
  invFun p := ⟨spinEquiv ⟨p.1, p.2.1.1, p.2.1.2⟩, by
    show IsShortCoord (coordOf (spinEquiv ⟨p.1, p.2.1.1, p.2.1.2⟩))
    rw [Griess.coordOf_spinEquiv]
    exact p.2.2⟩
  left_inv r := Subtype.ext (spinEquiv.apply_symm_apply r.1)
  right_inv p := Prod.ext (centralCoord_spinEquiv _)
    (Subtype.ext (Griess.coordOf_spinEquiv ⟨p.1, p.2.1.1, p.2.1.2⟩))

noncomputable def frameLiftEquiv :
    {r : Q | phi0 (coordOf r) ∈ frameDelta} ≃ ZMod 2 × (phi0 ⁻¹' frameDelta) where
  toFun r := (centralCoord r.1, ⟨coordOf r.1, r.2⟩)
  invFun p := ⟨spinEquiv ⟨p.1, p.2.1.1, p.2.1.2⟩, by
    show phi0 (coordOf (spinEquiv ⟨p.1, p.2.1.1, p.2.1.2⟩)) ∈ frameDelta
    rw [Griess.coordOf_spinEquiv]
    exact p.2.2⟩
  left_inv r := Subtype.ext (spinEquiv.apply_symm_apply r.1)
  right_inv p := Prod.ext (centralCoord_spinEquiv _)
    (Subtype.ext (Griess.coordOf_spinEquiv ⟨p.1, p.2.1.1, p.2.1.2⟩))

theorem ncard_shortInv : shortInv.ncard = 196560 := by
  rw [shortInv, Set.ncard_image_of_injective _ rhoEquiv_injective, ← Nat.card_coe_set_eq,
    Nat.card_congr shortLiftEquiv, Nat.card_prod, Nat.card_zmod, card_shortIdx]

theorem frameInv_eq_image :
    frameInv = rhoEquiv '' {r : Q | phi0 (coordOf r) ∈ frameDelta} := by
  have e : {r : Q | Multiplicative.toAdd (phi (QuotientGroup.mk r)) ∈ frameDelta} =
      {r : Q | phi0 (coordOf r) ∈ frameDelta} :=
    Set.ext fun r => mem_frameDelta_phi_iff r
  rw [frameInv, e]

theorem ncard_preimage_frameDelta : (phi0 ⁻¹' frameDelta).ncard = 8292375 := by
  rw [← Set.ncard_image_of_injective _ phi0_injective,
    Set.image_preimage_eq _ phi0_bijective.2, ncard_frameDelta]

theorem ncard_frameInv : frameInv.ncard = 16584750 := by
  rw [frameInv_eq_image, Set.ncard_image_of_injective _ rhoEquiv_injective, ← Nat.card_coe_set_eq,
    Nat.card_congr frameLiftEquiv, Nat.card_prod, Nat.card_zmod, Nat.card_coe_set_eq,
    ncard_preimage_frameDelta]

theorem gmul_unitB_eq_id : gmul unitB = LinearMap.id := LinearMap.ext gmul_unitB

theorem bform_axis_unitB {r : Q} (hr : IsShortCoord (coordOf r)) :
    bform (axis r) unitB = 1 / 2 := by
  rw [bform_comm, bform_axis_left hr]
  change qf (shortCls hr) ((4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ)) / 16 -
    2 * sgn (centralCoord r) * (0 : ℚ) = 1 / 2
  rw [qf_smul_one]
  norm_num

theorem bform_oneA_unitB : bform (inA oneA) unitB = 6 := by
  rw [bform_inA_oneA]
  change Matrix.trace ((4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ)) = 6
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  norm_num

theorem trace_rho_short {r : Q} (hr : IsShortCoord (coordOf r)) :
    LinearMap.trace ℚ SpaceB (rhoEquiv r : SpaceB →ₗ[ℚ] SpaceB) = 4372 := by
  have h := short_involution_axis_trace_identity r hr unitB
  rw [gmul_unitB_eq_id, LinearMap.comp_id, map_sub, map_smul, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, bform_oneA_unitB, bform_axis_unitB hr] at h
  rw [h]
  norm_num

theorem trace_xmat : LinearMap.trace ℚ SpaceB (xmat : SpaceB →ₗ[ℚ] SpaceB) = 276 := by
  rw [trace_prod_eq, trace_prod_eq]
  have hA : LinearMap.fst ℚ symMat (SpaceX × SpaceW) ∘ₗ (xmat : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ
      LinearMap.inl ℚ symMat (SpaceX × SpaceW) = LinearMap.id := by
    apply LinearMap.ext
    intro B
    rw [xmat_eq_xB]
    rfl
  have hX : LinearMap.fst ℚ SpaceX SpaceW ∘ₗ (LinearMap.snd ℚ symMat (SpaceX × SpaceW) ∘ₗ
      (xmat : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ LinearMap.inr ℚ symMat (SpaceX × SpaceW)) ∘ₗ
      LinearMap.inl ℚ SpaceX SpaceW = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rw [xmat_eq_xB]
    rfl
  have hW : LinearMap.snd ℚ SpaceX SpaceW ∘ₗ (LinearMap.snd ℚ symMat (SpaceX × SpaceW) ∘ₗ
      (xmat : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ LinearMap.inr ℚ symMat (SpaceX × SpaceW)) ∘ₗ
      LinearMap.inr ℚ SpaceX SpaceW = -LinearMap.id := by
    apply LinearMap.ext
    intro N
    rw [xmat_eq_xB]
    show (xB ((0 : symMat), (0 : SpaceX), N)).2.2 = -N
    rw [xB_apply]
  rw [hA, hX, hW, map_neg, LinearMap.trace_id, LinearMap.trace_id, LinearMap.trace_id, finrank_A,
    finrank_X, finrank_W]
  norm_num

theorem trace_conj (g t : SpaceB ≃ₗ[ℚ] SpaceB) :
    LinearMap.trace ℚ SpaceB ((g * t * g⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
      LinearMap.trace ℚ SpaceB (t : SpaceB →ₗ[ℚ] SpaceB) := by
  have e : ((g * t * g⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
      ((g : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ (t : SpaceB →ₗ[ℚ] SpaceB)) ∘ₗ
        (g.symm : SpaceB →ₗ[ℚ] SpaceB) := rfl
  rw [e, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc]
  have h1 : (g.symm : SpaceB →ₗ[ℚ] SpaceB) ∘ₗ (g : SpaceB →ₗ[ℚ] SpaceB) = LinearMap.id := by
    apply LinearMap.ext
    intro u
    exact g.symm_apply_apply u
  rw [h1, LinearMap.id_comp]

theorem rho_wQ_mem_frameInv : rhoEquiv wQ ∈ frameInv := by
  refine ⟨wQ, ?_, rfl⟩
  rw [Set.mem_ofPred_eq, phi_wQ]
  have e : classOf (fun _ : Fin 24 => (2 : ℤ)) = twoΩCls := by
    rw [classOf_of_mem' two_omega_mem]
    rfl
  rw [e]
  exact twoΩCls_mem_frameDelta

theorem exists_Gmat_conj_xmat
    {t : SpaceB ≃ₗ[ℚ] SpaceB} (ht : t ∈ frameInv) :
    ∃ g ∈ Gmat, g * xmat * g⁻¹ = t := by
  obtain ⟨g, hg, hgt⟩ := frameInv_transitive rho_wQ_mem_frameInv ht
  refine ⟨g * tauB ^ 2, mul_mem (Hmat_le_Gmat hg) (pow_mem tauB_mem_Gmat 2), ?_⟩
  have h2 : tauB ^ 2 * xmat * (tauB ^ 2)⁻¹ = rhoEquiv wQ :=
    triality_four_group_spin_identification.2.2.2.2.1
  calc g * tauB ^ 2 * xmat * (g * tauB ^ 2)⁻¹ = g * (tauB ^ 2 * xmat * (tauB ^ 2)⁻¹) * g⁻¹ := by
        group
    _ = t := by rw [h2, hgt]

theorem trace_of_mem_xF
    {t : SpaceB ≃ₗ[ℚ] SpaceB} (ht : t ∈ ({xmat} ∪ frameInv)) :
    LinearMap.trace ℚ SpaceB (t : SpaceB →ₗ[ℚ] SpaceB) = 276 := by
  rcases ht with h | h
  · rw [Set.mem_singleton_iff.1 h]
    exact trace_xmat
  · obtain ⟨g, -, rfl⟩ := exists_Gmat_conj_xmat h
    rw [trace_conj]
    exact trace_xmat

theorem trace_of_mem_shortInv
    {t : SpaceB ≃ₗ[ℚ] SpaceB} (ht : t ∈ shortInv) :
    LinearMap.trace ℚ SpaceB (t : SpaceB →ₗ[ℚ] SpaceB) = 4372 := by
  obtain ⟨r, hr, rfl⟩ := ht
  exact trace_rho_short hr

theorem xF_conj
    {s t : SpaceB ≃ₗ[ℚ] SpaceB} (hs : s ∈ ({xmat} ∪ frameInv))
    (ht : t ∈ ({xmat} ∪ frameInv)) : ∃ g ∈ Gmat, g * s * g⁻¹ = t := by
  have hx : ∀ {u : SpaceB ≃ₗ[ℚ] SpaceB}, u ∈ ({xmat} ∪ frameInv) → ∃ g ∈ Gmat, g * xmat * g⁻¹ = u := by
    intro u hu
    rcases hu with h | h
    · exact ⟨1, one_mem _, by rw [Set.mem_singleton_iff.1 h]; group⟩
    · exact exists_Gmat_conj_xmat h
  obtain ⟨a, ha, rfl⟩ := hx hs
  obtain ⟨b, hb, rfl⟩ := hx ht
  refine ⟨b * a⁻¹, mul_mem hb (inv_mem ha), ?_⟩
  group

theorem spin_involution_visible_orbits_and_fusion :
    involQmat = {xmat} ∪ shortInv ∪ frameInv ∧
    xmat ∉ shortInv ∧ xmat ∉ frameInv ∧ Disjoint shortInv frameInv ∧
    (∀ g ∈ Gvis, g * xmat * g⁻¹ = xmat) ∧
    (∀ g ∈ Gvis, ∀ t ∈ shortInv, g * t * g⁻¹ ∈ shortInv) ∧
    (∀ g ∈ Gvis, ∀ t ∈ frameInv, g * t * g⁻¹ ∈ frameInv) ∧
    (∀ s ∈ shortInv, ∀ t ∈ shortInv, ∃ g ∈ Gvis, g * s * g⁻¹ = t) ∧
    (∀ s ∈ frameInv, ∀ t ∈ frameInv, ∃ g ∈ Gvis, g * s * g⁻¹ = t) ∧
    ({xmat} : Set (SpaceB ≃ₗ[ℚ] SpaceB)).ncard = 1 ∧ shortInv.ncard = 196560 ∧
    frameInv.ncard = 16584750 ∧
    (∀ s ∈ involQmat, ∀ t ∈ involQmat, (∃ g ∈ Gmat, g * s * g⁻¹ = t) ↔
      ((s ∈ shortInv ∧ t ∈ shortInv) ∨ (s ∈ ({xmat} ∪ frameInv) ∧ t ∈ ({xmat} ∪ frameInv)))) ∧
    (∀ t ∈ shortInv, LinearMap.trace ℚ SpaceB (t : SpaceB →ₗ[ℚ] SpaceB) = 4372) ∧
    (∀ t ∈ ({xmat} ∪ frameInv), LinearMap.trace ℚ SpaceB (t : SpaceB →ₗ[ℚ] SpaceB) = 276) := by
  refine ⟨involQmat_eq, xmat_not_mem_shortInv, xmat_not_mem_frameInv, disjoint_shortInv_frameInv,
    fun g hg => Gvis_conj_xmat hg, fun g hg t ht => Gvis_conj_mem_shortInv hg ht,
    fun g hg t ht => Gvis_conj_mem_frameInv hg ht, fun s hs t ht => shortInv_transitive hs ht,
    fun s hs t ht => frameInv_transitive hs ht, Set.ncard_singleton _, ncard_shortInv,
    ncard_frameInv, ?_, fun t ht => trace_of_mem_shortInv ht, fun t ht => trace_of_mem_xF ht⟩
  intro s hs t ht
  have hsplit : ∀ {u : SpaceB ≃ₗ[ℚ] SpaceB}, u ∈ involQmat → u ∈ shortInv ∨ u ∈ ({xmat} ∪ frameInv) := by
    intro u hu
    rw [involQmat_eq] at hu
    rcases hu with (h | h) | h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)
  constructor
  · rintro ⟨g, -, rfl⟩
    rcases hsplit hs with h1 | h1 <;> rcases hsplit ht with h2 | h2
    · exact .inl ⟨h1, h2⟩
    · exfalso
      have e1 := trace_of_mem_shortInv h1
      have e2 := trace_of_mem_xF h2
      rw [trace_conj, e1] at e2
      norm_num at e2
    · exfalso
      have e1 := trace_of_mem_xF h1
      have e2 := trace_of_mem_shortInv h2
      rw [trace_conj, e1] at e2
      norm_num at e2
    · exact .inr ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · obtain ⟨g, hg, h⟩ := shortInv_transitive h1 h2
      exact ⟨g, Hmat_le_Gmat hg, h⟩
    · exact xF_conj h1 h2

end CFSG.Monster.B
