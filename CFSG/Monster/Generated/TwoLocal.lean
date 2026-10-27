module

public import CFSG.Monster.Generated.Centralizer
public import CFSG.Monster.Generated.GreyEscape
public import CFSG.Monster.Generated.OddCocode
public import CFSG.Monster.Visible.Irreducible
public import CFSG.Monster.TrialitySubgroup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Generated

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.ScalarKernel

open scoped IsMulCommutative commutatorElement


instance normal_Qmat_subgroupOf_Hmat : (Qmat.subgroupOf Hmat).Normal := normal_rhoQ_subgroupOf

theorem rhoEquiv_zpow (r : Q) (k : ℤ) : rhoEquiv (r ^ k) = rhoEquiv r ^ k := by
  have h := congrArg MulOpposite.unop (map_zpow rho r k)
  rw [MulOpposite.unop_zpow] at h
  exact h

theorem rhoEquiv_inv (r : Q) : rhoEquiv r⁻¹ = (rhoEquiv r)⁻¹ := by
  have h := rhoEquiv_zpow r (-1)
  rwa [zpow_neg_one, zpow_neg_one] at h

theorem rhoEquiv_one : rhoEquiv 1 = 1 := by
  have h := rhoEquiv_zpow 1 0
  rwa [zpow_zero, zpow_zero] at h

theorem rhoEquiv_mem_zpowers_iff (r : Q) :
    rhoEquiv r ∈ Subgroup.zpowers xmat ↔ r ∈ Subgroup.zpowers zQ := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, rhoEquiv_injective ?_⟩
    rw [rhoEquiv_zpow]
    exact hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, (rhoEquiv_zpow zQ k).symm⟩

theorem coordOf_one' : coordOf (1 : Q) = 0 :=
  (mem_zpowers_zQ_iff 1).1 (Subgroup.one_mem _)

theorem coordOf_inv' (r : Q) : coordOf r⁻¹ = coordOf r := by
  have h := coordOf_mul r⁻¹ r
  rw [inv_mul_cancel, coordOf_one'] at h
  exact (eq_of_add_eq_zero' h.symm).symm

theorem inv_mul_mem_zpowers_zQ_iff (t t' : Q) :
    t⁻¹ * t' ∈ Subgroup.zpowers zQ ↔ coordOf t = coordOf t' := by
  rw [mem_zpowers_zQ_iff, coordOf_mul, coordOf_inv']
  constructor
  · intro h
    exact (eq_of_add_eq_zero' h).symm
  · intro h
    rw [h]
    exact add_self_eq_zero_of_char_two (coordOf t')
where
  add_self_eq_zero_of_char_two (x : C × Cocode) : x + x = 0 := by
    rw [← two_smul (ZMod 2) x]
    exact (show (2 : ZMod 2) = 0 from rfl) ▸ zero_smul (ZMod 2) x

theorem orderOf_xmat : orderOf xmat = 2 := by
  rw [xmat_eq_xB]
  exact orderOf_eq_prime (by rw [pow_two, xB_mul_self]) xB_ne_one

theorem center_Qmat : ∀ q ∈ Qmat, (∀ x ∈ Qmat, x * q = q * x) ↔ q ∈ Subgroup.zpowers xmat := by
  intro q hq
  obtain ⟨r, rfl⟩ := mem_rhoQ.1 hq
  rw [rhoEquiv_mem_zpowers_iff, ← center_Q, Subgroup.mem_center_iff]
  constructor
  · intro h s
    apply rhoEquiv_injective
    have := h (rhoEquiv s) (rhoEquiv_mem_rhoQ s)
    rw [rhoEquiv_mul, rhoEquiv_mul]
    exact this.symm
  · intro h x hx
    obtain ⟨s, rfl⟩ := mem_rhoQ.1 hx
    rw [← rhoEquiv_mul, ← rhoEquiv_mul, h s]

private theorem inv_mul_inv_mul_eq_commutator {M : Type*} [Group M] (s t : M) :
    t⁻¹ * s⁻¹ * t * s = ⁅t⁻¹, s⁻¹⁆ := by
  rw [commutatorElement_def, inv_inv, inv_inv]

theorem comm_Qmat : ∀ x ∈ Qmat, ∀ y ∈ Qmat, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers xmat := by
  rintro _ hx _ hy
  obtain ⟨s, rfl⟩ := mem_rhoQ.1 hx
  obtain ⟨t, rfl⟩ := mem_rhoQ.1 hy
  have e : rhoEquiv s * rhoEquiv t * (rhoEquiv s)⁻¹ * (rhoEquiv t)⁻¹ =
      rhoEquiv (t⁻¹ * s⁻¹ * t * s) := by
    rw [← rhoEquiv_inv, ← rhoEquiv_inv, rhoEquiv_mul, rhoEquiv_mul, rhoEquiv_mul]
    simp only [mul_assoc]
  rw [e, rhoEquiv_mem_zpowers_iff, inv_mul_inv_mul_eq_commutator s t]
  exact (le_of_eq commutator_Q)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem exists_Qmat_not_mem_zpowers : ∃ q ∈ Qmat, q ∉ Subgroup.zpowers xmat := by
  set δ : Cocode := Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2))
  refine ⟨rhoEquiv (DQ δ), rhoEquiv_mem_rhoQ _, ?_⟩
  rw [rhoEquiv_mem_zpowers_iff, mem_zpowers_zQ_iff, DQ_eq, Griess.coordOf_spinEquiv]
  intro h
  have hδ : δ = 0 := congrArg Prod.snd h
  have h1 := odd_cocode_inverts_triality.2.1
  rw [show (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2)) : Cocode) = δ from rfl,
    hδ, pair_zero_right] at h1
  exact zero_ne_one h1

theorem faithful_Hmat : ∀ f ∈ Hmat,
    (∀ x ∈ Qmat, f * x * f⁻¹ * x⁻¹ ∈ Subgroup.zpowers xmat) → f ∈ Qmat := by
  intro f hf hc
  obtain ⟨p, rfl⟩ := mem_Gvis.1 hf
  have h1 : conjVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ = 1 := by
    rw [conjVis_eq_one_iff]
    intro x
    obtain ⟨t, rfl⟩ := rhoN_surjective x
    rw [conjNormal_thetaEquiv_rhoN, mk_rhoN_eq_iff]
    have h := hc (rhoEquiv t) (rhoEquiv_mem_rhoQ t)
    rw [thetaEquiv_conj_rhoEquiv, ← rhoEquiv_inv, ← rhoEquiv_mul, rhoEquiv_mem_zpowers_iff,
      inv_mul_mem_zpowers_zQ_iff] at h
    exact h.symm
  have h2 : (⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ : Gvis) ∈ rhoQvis := by
    rw [← ker_conjVis]
    exact h1
  exact h2

theorem irreducible_Qmat
    (hirr : ∀ W : Submodule (ZMod 2) (Additive VisMod),
      (∀ g : Gvis ⧸ rhoQvis, ∀ w ∈ W,
        ((repQuot g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
          Additive VisMod →ₗ[ZMod 2] Additive VisMod) w ∈ W) → W = ⊥ ∨ W = ⊤)
    (R : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)) (hR : ∀ f ∈ Hmat, ∀ r ∈ R, f * r * f⁻¹ ∈ R)
    (hzR : Subgroup.zpowers xmat ≤ R) (hRQ : R ≤ Qmat) :
    R = Subgroup.zpowers xmat ∨ R = Qmat := by
  let W₂ : Submodule (ZMod 2) L2 :=
    { carrier := {v | ∃ t : Q, rhoEquiv t ∈ R ∧ v = phi0 (coordOf t)}
      add_mem' := by
        rintro _ _ ⟨t₁, h₁, rfl⟩ ⟨t₂, h₂, rfl⟩
        refine ⟨t₁ * t₂, ?_, ?_⟩
        · rw [rhoEquiv_mul]
          exact R.mul_mem h₂ h₁
        · rw [coordOf_mul, map_add]
      zero_mem' := ⟨1, by rw [rhoEquiv_one]; exact R.one_mem, by rw [coordOf_one', map_zero]⟩
      smul_mem' := by
        rintro c _ ⟨t, ht, rfl⟩
        rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) c with rfl | rfl
        · refine ⟨1, by rw [rhoEquiv_one]; exact R.one_mem, ?_⟩
          rw [zero_smul, coordOf_one', map_zero]
        · rw [one_smul]
          exact ⟨t, ht, rfl⟩ }
  let W : Submodule (ZMod 2) (Additive VisMod) :=
    W₂.comap (visModLat : Additive VisMod →ₗ[ZMod 2] L2)
  have hlat : ∀ t : Q, visModLat (Additive.ofMul (QuotientGroup.mk (rhoN t) : VisMod)) =
      phi0 (coordOf t) := fun t => (visModLat_mk t).trans (toAdd_phi_mk t)
  have hconj : ∀ (p : Pvis) (t : Q),
      modTwoEnd p.1.2 (phi0 (coordOf t)) = phi0 (coordOf (conjQ p t)) := fun p t =>
    (congrArg (modTwoEnd p.1.2) (toAdd_phi_mk t).symm).trans
      ((phi_conjQ p t).symm.trans (toAdd_phi_mk (conjQ p t)))
  have hW : ∀ g : Gvis ⧸ rhoQvis, ∀ w ∈ W,
      ((repQuot g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
        Additive VisMod →ₗ[ZMod 2] Additive VisMod) w ∈ W := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      intro w hw
      obtain ⟨p, rfl⟩ := eq_thetaEquiv g
      change visModLat (((repVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ :
        LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
          Additive VisMod →ₗ[ZMod 2] Additive VisMod) w) ∈ W₂
      rw [visModLat_repVis]
      obtain ⟨t, ht, he⟩ := hw
      change modTwoEnd p.1.2 (visModLat w) ∈ W₂
      rw [LinearEquiv.coe_coe] at he
      rw [he, hconj]
      refine ⟨conjQ p t, ?_, rfl⟩
      rw [← thetaEquiv_conj_rhoEquiv]
      exact hR _ (thetaEquiv_mem_Gvis p) _ ht
  have hmemW : ∀ t : Q, Additive.ofMul (QuotientGroup.mk (rhoN t) : VisMod) ∈ W ↔
      phi0 (coordOf t) ∈ W₂ := fun t => by
    change visModLat _ ∈ W₂ ↔ _
    rw [hlat]
  have hmk : ∀ t t' : Q, phi0 (coordOf t) = phi0 (coordOf t') →
      t⁻¹ * t' ∈ Subgroup.zpowers zQ := fun t t' h =>
    (inv_mul_mem_zpowers_zQ_iff t t').2 (phi0_bijective.1 h)
  rcases hirr W hW with h | h
  · left
    refine le_antisymm (fun r hr => ?_) hzR
    obtain ⟨t, rfl⟩ := mem_rhoQ.1 (hRQ hr)
    have hmem := (hmemW t).2 ⟨t, hr, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    have h0 : phi0 (coordOf t) = phi0 (coordOf (1 : Q)) := by
      rw [← hlat, hmem, coordOf_one', map_zero, map_zero]
    have h1 := hmk t 1 h0
    rw [mul_one] at h1
    rw [rhoEquiv_mem_zpowers_iff]
    simpa using (Subgroup.zpowers zQ).inv_mem h1
  · right
    refine le_antisymm hRQ fun q hq => ?_
    obtain ⟨t, rfl⟩ := mem_rhoQ.1 hq
    have hmem : Additive.ofMul (QuotientGroup.mk (rhoN t) : VisMod) ∈ W := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨t', ht', he⟩ := (hmemW t).1 hmem
    have hz : rhoEquiv (t'⁻¹ * t) ∈ R :=
      hzR ((rhoEquiv_mem_zpowers_iff _).2 (hmk t' t he.symm))
    have e : rhoEquiv t = rhoEquiv (t'⁻¹ * t) * rhoEquiv t' := by
      rw [← rhoEquiv_mul, mul_inv_cancel_left]
    rw [e]
    exact R.mul_mem hz ht'

theorem conj_tauB_mem_Vmat : ∀ e ∈ Vmat, tauB * e * tauB⁻¹ ∈ Vmat := by
  intro e he
  rcases mem_Vmat.1 he with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact Vmat.one_mem
  · rw [generated_rational_group_finite_centralizer.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact mem_Vmat.2 (.inr (.inr (.inl rfl)))
  · rw [generated_rational_group_finite_centralizer.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact mem_Vmat.2 (.inr (.inr (.inr rfl)))
  · rw [generated_rational_group_finite_centralizer.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
    exact mem_Vmat.2 (.inr (.inl rfl))

theorem conj_tauB_ne : ∀ e ∈ Vmat, e ≠ 1 → tauB * e * tauB⁻¹ ≠ e := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hxy, hxz, hyz, cx, cy, cz⟩ :=
    generated_rational_group_finite_centralizer
  intro e he hne
  rcases mem_Vmat.1 he with rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · rw [cx]
    exact Ne.symm hxy
  · rw [cy]
    exact Ne.symm hyz
  · rw [cz]
    exact hxz

theorem closure_insert_tauB_inv_Hmat :
    Subgroup.closure (insert tauB⁻¹ (Hmat : Set (SpaceB ≃ₗ[ℚ] SpaceB))) = Gmat := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro f (rfl | hf)
    · exact inv_mem tauB_mem_Gmat
    · exact Hmat_le_Gmat hf
  · rw [Gmat, Subgroup.closure_le]
    rintro f (hf | hf)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hf)
    · rw [Set.mem_singleton_iff.1 hf, ← inv_inv tauB]
      exact inv_mem (Subgroup.subset_closure (Set.mem_insert _ _))

theorem generated_group_two_local_simplicity_reduction
    (hsimple : IsSimpleGroup (Hmat ⧸ Qmat.subgroupOf Hmat))
    (hirr : ∀ W : Submodule (ZMod 2) (Additive VisMod),
      (∀ g : Gvis ⧸ rhoQvis, ∀ w ∈ W,
        ((repQuot g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
          Additive VisMod →ₗ[ZMod 2] Additive VisMod) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Nontrivial Gmat ∧ IsSimpleGroup Gmat ∧ Finite Gmat := by
  obtain ⟨hGA, hfin, hCz, hVH, hV4, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    generated_rational_group_finite_centralizer
  have hdelta : rhoEquiv (DQ (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2)))) ∈
      Hmat := odd_cocode_inverts_triality.2.2.1
  obtain ⟨-, hsq, hrel, hrel2, -⟩ :=
    odd_cocode_inverts_triality.1 _ odd_cocode_inverts_triality.2.1
  set h := rhoEquiv (DQ (Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2))))
  have e1 : tauB * h * tauB⁻¹ = h * tauB := by
    calc tauB * h * tauB⁻¹ = (h * h) * (tauB * h * tauB⁻¹) := by rw [hsq, one_mul]
      _ = h * (h * (tauB * h * tauB⁻¹)) := by rw [mul_assoc]
      _ = h * tauB := by rw [hrel2]
  have hhτ : tauB⁻¹⁻¹ * h * tauB⁻¹ * h = tauB⁻¹ := by
    rw [inv_inv, e1]
    exact hrel
  obtain ⟨-, -, -, -, -, hu, huH, huQ, -, -⟩ := grey_translation_triality_escape
  have hmain := isSimpleGroup_of_triality_subgroup (K := Gmat) (H := Hmat) (Q := Qmat)
    Hmat_le_Gmat Qmat_le_Hmat xmat_mem_Qmat orderOf_xmat center_Qmat comm_Qmat
    exists_Qmat_not_mem_zpowers hsimple faithful_Hmat (irreducible_Qmat hirr) hCz
    (E := Vmat) hVH hV4 (fun e he => sq_of_mem_fourGroupB he) (mem_Vmat.2 (.inr (.inl rfl)))
    (τ := tauB⁻¹) (inv_mem tauB_mem_Gmat)
    (fun e he => by rw [inv_inv]; exact conj_tauB_mem_Vmat e he)
    (fun e he hne => by rw [inv_inv]; exact conj_tauB_ne e he hne)
    closure_insert_tauB_inv_Hmat (u := greyTrans) hu (by rw [inv_inv]; exact huH)
    (by rw [inv_inv]; exact huQ) (h := h) hdelta hhτ
  exact ⟨hmain.1, hmain.2, hfin⟩

end CFSG.Monster.Generated
