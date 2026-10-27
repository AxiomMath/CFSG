module

public import CFSG.Monster.B.Cbar.FourGroupBar
public import CFSG.Monster.B.Cbar.Fusion
public import CFSG.Monster.B.Short.ParityCentralizer
public import CFSG.Monster.B.Cbar.LocalE

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot

theorem isShortCoord_zQ_mul_rStar : IsShortCoord (coordOf (zQ * rStar)) :=
  isShortCoord_zQ_mul isShortCoord_rStar

theorem Jbar_le_centralizer_xbar : Jbar ≤ Subgroup.centralizer {xbar} := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hgv : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := hg.1
  have hc : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Subgroup.centralizer {xmat} := by
    have : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat ⊓ Subgroup.centralizer {xmat} := by
      rw [Gmat_inf_centralizer_xmat]
      exact hgv
    exact this.2
  have hc' : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat = xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB) :=
    Subgroup.mem_centralizer_singleton_iff.1 hc
  have hC : g * xC = xC * g := Subtype.ext hc'
  rw [xbar, ← map_mul, ← map_mul, hC]

theorem centralizer_xbar_le_Jbar :
    Subgroup.centralizer {xbar} ≤ Jbar := by
  intro c hc
  obtain ⟨g, rfl⟩ := kappa_surjective c
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have h1 : kappa (g * xC * g⁻¹ * xC⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    change kappa g * xbar * (kappa g)⁻¹ * xbar⁻¹ = 1
    rw [hc]
    group
  have hcomm : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = xmat := by
    rcases (kappa_eq_one_iff _).1 h1 with h2 | h2
    · have h3 := congrArg Subtype.val h2
      change (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat⁻¹ = 1 at h3
      exact mul_inv_eq_one.1 h3
    · exfalso
      have h3 := congrArg Subtype.val h2
      change (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat⁻¹ = tStar at h3
      have h4 : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ =
          rhoEquiv (zQ * rStar) := by
        rw [← tStar_mul_xmat, ← h3]
        group
      have e1 := trace_conj (g : SpaceB ≃ₗ[ℚ] SpaceB) xmat
      rw [h4, trace_rho_short isShortCoord_zQ_mul_rStar, trace_xmat] at e1
      norm_num at e1
  have hgx : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat ⊓ Subgroup.centralizer {xmat} := by
    refine ⟨Cgen_le_Gmat g.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat =
        (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
          (g : SpaceB ≃ₗ[ℚ] SpaceB) := by group
      _ = xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB) := by rw [hcomm]
  rw [Gmat_inf_centralizer_xmat] at hgx
  exact ⟨g, ⟨hgx, Subgroup.mem_centralizer_singleton_iff.2 (commute_tStar_of_mem_Cgen g.2)⟩, rfl⟩

theorem centralizer_xbar : Subgroup.centralizer {xbar} = Jbar :=
  le_antisymm centralizer_xbar_le_Jbar Jbar_le_centralizer_xbar

theorem natCard_zpowers_tJ : Nat.card (Subgroup.zpowers (tJ rStar)) = 2 := by
  rw [Nat.card_zpowers, orderOf_tJ isShortCoord_rStar]

theorem natCard_Jbar :
    Nat.card Jbar = 354883595661213696000 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (tJ rStar))
  rw [natCard_Jmat isShortCoord_rStar, natCard_zpowers_tJ] at h1
  rw [← Nat.card_congr jEquiv.toEquiv]
  omega

theorem piK_surjective :
    Function.Surjective piK := by
  intro k
  have hk : MulOpposite.op ((k : OLq)⁻¹) ∈ (piJ rStar).range := by
    rw [range_piJ isShortCoord_rStar]
    exact Subgroup.inv_mem _ k.2
  obtain ⟨f, hf⟩ := hk
  refine ⟨f, Subtype.ext ?_⟩
  change (MulOpposite.unop (piJ rStar f))⁻¹ = k
  rw [hf, MulOpposite.unop_op, inv_inv]

theorem jbarToKv_surjective :
    Function.Surjective jbarToKv :=
  (QuotientGroup.lift_surjective_of_surjective _ _ piK_surjective zpowers_tJ_le_ker_piK).comp
    jEquiv.symm.surjective

@[expose] noncomputable def xq : Equot rStar :=
  ⟨QuotientGroup.mk (xJ rStar), mk_xJ_mem_Equot rStar⟩

theorem eEquiv_xq : eEquiv xq = ⟨xbar, xbar_mem_Ebar⟩ := Subtype.ext rfl

theorem orderOf_xbarE : orderOf (⟨xbar, xbar_mem_Ebar⟩ : Ebar) = 2 := by
  have h := orderOf_injective Ebar.subtype Subtype.coe_injective ⟨xbar, xbar_mem_Ebar⟩
  rw [Subgroup.coe_subtype] at h
  rw [← h]
  exact orderOf_xbar

theorem center_Ebar : Subgroup.center Ebar = Subgroup.zpowers ⟨xbar, xbar_mem_Ebar⟩ := by
  obtain ⟨-, -, hcen, -, -⟩ := equot_facts isShortCoord_rStar
  have h := center_eq_zpowers_of_mulEquiv eEquiv hcen
  rw [show eEquiv ⟨QuotientGroup.mk (xJ rStar), mk_xJ_mem_Equot rStar⟩ = ⟨xbar, xbar_mem_Ebar⟩
    from eEquiv_xq] at h
  exact h

theorem Ebar_extraspecial : IsExtraspecialPGroup 2 Ebar ∧ Nat.card Ebar = 2 ^ 23 := by
  obtain ⟨hE, hcard, hcen, hcomm, hfr⟩ := equot_facts isShortCoord_rStar
  have hcomm' := commutator_eq_zpowers_of_mulEquiv eEquiv hcomm
  have hfr' := frattini_eq_zpowers_of_mulEquiv eEquiv hfr
  have e : eEquiv ⟨QuotientGroup.mk (xJ rStar), mk_xJ_mem_Equot rStar⟩ = ⟨xbar, xbar_mem_Ebar⟩ :=
    eEquiv_xq
  rw [e] at hcomm' hfr'
  refine ⟨⟨IsPGroup.of_equiv hE.1 eEquiv, hcomm'.trans center_Ebar.symm,
    hfr'.trans center_Ebar.symm, ?_⟩, ?_⟩
  · rw [center_Ebar, Nat.card_zpowers, orderOf_xbarE]
  · rw [← Nat.card_congr eEquiv.toEquiv, hcard]

theorem map_center_Ebar : (Subgroup.center Ebar).map Ebar.subtype = Subgroup.zpowers xbar := by
  rw [center_Ebar, MonoidHom.map_zpowers]
  rfl

theorem centralizer_Ebar :
    Jbar ⊓ Subgroup.centralizer (Ebar : Set Cbar) = Subgroup.zpowers xbar := by
  apply le_antisymm
  · rintro c ⟨hcJ, hcC⟩
    obtain ⟨g, hg, rfl⟩ := hcJ
    have hmem := mem_rhoCQ_of_commute_Ebar (Subgroup.mem_subgroupOf.1 hg)
      (Subgroup.mem_centralizer_iff.1 hcC)
    have hcE : kappa g ∈ Ebar := ⟨g, hmem, rfl⟩
    have hcen : (⟨kappa g, hcE⟩ : Ebar) ∈ Subgroup.center Ebar := by
      rw [Subgroup.mem_center_iff]
      intro e
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hcC _ e.2)
    rw [center_Ebar] at hcen
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcen
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by
      have := congrArg Subtype.val hk
      rwa [SubgroupClass.coe_zpow] at this⟩
  · rw [Subgroup.zpowers_le]
    refine ⟨xbar_mem_Jbar, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    have hx : (⟨xbar, xbar_mem_Ebar⟩ : Ebar) ∈ Subgroup.center Ebar := by
      rw [center_Ebar]
      exact Subgroup.mem_zpowers _
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hx) ⟨e, he⟩)

theorem ker_psiBar : psiBar.ker = Subgroup.center Ebar := by
  ext e
  rw [MonoidHom.mem_ker, psiBar_eq_one_iff, center_Ebar,
    Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbarE]

@[expose] noncomputable def ebarQuotEquiv :
    Ebar ⧸ Subgroup.center Ebar ≃* Multiplicative (Wv (phi0 (coordOf rStar))) :=
  (QuotientGroup.quotientMulEquivOfEq ker_psiBar.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective psiBar psiBar_surjective)

theorem ebarQuotEquiv_mk (e : Ebar) : ebarQuotEquiv (QuotientGroup.mk e) = psiBar e := rfl

theorem center_Cbar : Subgroup.center Cbar = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have hcomm := Subgroup.mem_center_iff.1 hc
  have hcJ : c ∈ Jbar := by
    rw [← centralizer_xbar]
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm xbar).symm
  have hcE : c ∈ Jbar ⊓ Subgroup.centralizer (Ebar : Set Cbar) :=
    ⟨hcJ, Subgroup.mem_centralizer_iff.2 fun e _ => hcomm e⟩
  rw [centralizer_Ebar, Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbar] at hcE
  rcases hcE with h | h
  · exact h
  · exfalso
    subst h
    have h1 : taubar * xbar * taubar⁻¹ = xbar := by
      rw [hcomm taubar, mul_inv_cancel_right]
    exact xbar_ne_ybar (h1.symm.trans taubar_conj_xbar)

theorem short_centralizer_quotient_local_structure :
    Multiplicative.toAdd (phi (QuotientGroup.mk rStar)) = phi0 (coordOf rStar) ∧
    orderOf xbar = 2 ∧ Subgroup.centralizer {xbar} = Jbar ∧
    Ebar ≤ Jbar ∧ Function.Surjective jbarToKv ∧ jbarToKv.ker = Ebar.subgroupOf Jbar ∧
    Nat.card Jbar = 354883595661213696000 ∧
    IsExtraspecialPGroup 2 Ebar ∧ Nat.card Ebar = 2 ^ 23 ∧ (Ebar.subgroupOf Jbar).Normal ∧
    (Subgroup.center Ebar).map Ebar.subtype = Subgroup.zpowers xbar ∧
    Jbar ⊓ Subgroup.centralizer (Ebar : Set Cbar) = Subgroup.zpowers xbar ∧
    Function.Surjective psiBar ∧ psiBar.ker = Subgroup.center Ebar ∧
    (∀ e : Ebar, ebarQuotEquiv (QuotientGroup.mk e) = psiBar e) ∧
    (∀ (q : Q) (hq : q ∈ Subgroup.centralizer {rStar}),
      psiBar ⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩, kappa_rho_mem_Ebar hq⟩ =
        Multiplicative.ofAdd (Submodule.Quotient.mk ⟨phi0 (coordOf q), phi0_mem_vPerpL rfl hq⟩)) ∧
    (∀ (g e : Cbar) (hg : g ∈ Jbar) (he : e ∈ Ebar),
      psiBar ⟨g⁻¹ * e * g, conj_mem_Ebar hg he⟩ =
        Multiplicative.ofAdd (wAct _ (jbarToKv ⟨g, hg⟩) (Multiplicative.toAdd (psiBar ⟨e, he⟩)))) ∧
    Function.Injective (KvAct (phi0 (coordOf rStar))) ∧
    (∀ (g : Cbar) (hg : g ∈ Jbar), (∀ (e : Cbar) (he : e ∈ Ebar),
      psiBar ⟨g⁻¹ * e * g, conj_mem_Ebar hg he⟩ = psiBar ⟨e, he⟩) → g ∈ Ebar) ∧
    orderOf taubar = 3 ∧ IsKleinFour Vbar ∧ xbar ∈ Vbar ∧
    (∀ c, c ∈ Vbar ↔ c = 1 ∨ c = xbar ∨ c = ybar ∨ c = zbar) ∧
    xbar ≠ ybar ∧ ybar ≠ zbar ∧ zbar ≠ xbar ∧
    taubar * xbar * taubar⁻¹ = ybar ∧ taubar * ybar * taubar⁻¹ = zbar ∧
    taubar * zbar * taubar⁻¹ = xbar ∧
    Subgroup.center Cbar = ⊥ :=
  ⟨toAdd_phi_mk rStar, orderOf_xbar, centralizer_xbar, Ebar_le_Jbar, jbarToKv_surjective,
    ker_jbarToKv, natCard_Jbar, Ebar_extraspecial.1, Ebar_extraspecial.2, inferInstance,
    map_center_Ebar, centralizer_Ebar, psiBar_surjective, ker_psiBar, ebarQuotEquiv_mk,
    fun _ hq => psiBar_kappa_rho hq, fun _ _ hg he => psiBar_conj hg he, KvAct_injective_rStar,
    fun _ hg h => mem_Ebar_of_conj_trivial hg h, orderOf_taubar, isKleinFour_Vbar, xbar_mem_Vbar,
    mem_Vbar_iff, xbar_ne_ybar, ybar_ne_zbar, zbar_ne_xbar, taubar_conj_xbar, taubar_conj_ybar,
    taubar_conj_zbar, center_Cbar⟩

end CFSG.Monster.B
