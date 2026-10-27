module

public import CFSG.Monster.Existence.TwoB
public import CFSG.Monster.Schur.GmatStructureExtraspecial

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.B Subgroup

theorem isExtraspecialAmbient_Qmat : IsExtraspecialAmbient Qmat xmat := by
  have h1 : CFSG.IsExtraspecialPGroup 2 Qmat :=
    CFSG.Monster.Existence.IsExtraspecialPGroup.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe rhoQ_le_Gvis)
      CFSG.Monster.Existence.isExtraspecialPGroup_rhoQvis
  refine IsExtraspecialAmbient.of_isExtraspecialPGroup h1 xmat_mem_Qmat ?_ ?_
  · rw [xmat_eq_xB]
    exact one_ne_xB.symm
  · intro g hg
    have hx : xmat ∈ Gmat ⊓ Subgroup.centralizer (Qmat : Set (SpaceB ≃ₗ[ℚ] SpaceB)) := by
      rw [CFSG.Monster.Existence.Gmat_inf_centralizer_Qmat]
      exact Subgroup.mem_zpowers xmat
    exact Subgroup.mem_centralizer_iff.1 hx.2 g hg

@[expose] def PhiV : Gvis →* GLV := opQHom.comp piVis

theorem PhiV_thetaEquiv (p : Pvis) :
    PhiV ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ = modTwoUnit p.1.2 := by
  show opQHom (piVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩) = _
  rw [piVis_thetaEquiv]
  rfl

theorem PhiV_mem_Hvis
    (g : Gvis) : PhiV g ∈ Hvis := by
  rw [← range_opQHom]
  exact ⟨piVis g, rfl⟩

@[expose] def PhiH :
    Gvis →* Hvis := PhiV.codRestrict Hvis PhiV_mem_Hvis

theorem coe_PhiH
    (g : Gvis) : ((PhiH g : Hvis) : GLV) = PhiV g := rfl

theorem ker_PhiV : PhiV.ker = rhoQvis := by
  rw [PhiV, MonoidHom.ker_comp_of_injective _ _ opQHom_injective, ker_piVis]

theorem PhiV_eq_one_iff {g : Gvis} : PhiV g = 1 ↔ (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Qmat := by
  rw [← MonoidHom.mem_ker, ker_PhiV]
  exact Subgroup.mem_subgroupOf

theorem exists_PhiV_eq
    {ν : GLV} (hν : ν ∈ Hvis) : ∃ g : Gvis, PhiV g = ν := by
  rw [← range_opQHom] at hν
  obtain ⟨y, rfl⟩ := hν
  have : y ∈ piVis.range := by
    rw [range_piVis]
    trivial
  obtain ⟨g, rfl⟩ := this
  exact ⟨g, rfl⟩

theorem PhiH_surjective :
    Function.Surjective PhiH := by
  intro ν
  obtain ⟨g, hg⟩ := exists_PhiV_eq ν.2
  exact ⟨g, Subtype.ext hg⟩

@[expose] def imPhi (S : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)) : Subgroup GLV :=
  (S.subgroupOf Gvis).map PhiV

theorem mem_imPhi {S : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} {ν : GLV} :
    ν ∈ imPhi S ↔ ∃ (g : SpaceB ≃ₗ[ℚ] SpaceB) (hg : g ∈ Gvis), g ∈ S ∧ PhiV ⟨g, hg⟩ = ν := by
  rw [imPhi, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, g.2, hg, rfl⟩
  · rintro ⟨g, hg, hgS, rfl⟩
    exact ⟨⟨g, hg⟩, hgS, rfl⟩

theorem xmatTau_eq_rho : xmatTau = rhoEquiv (zQ * wQ) := by
  rw [xmatTau_eq, rhoEquiv_zQ_wQ]

theorem zQ_mem_center : zQ ∈ Subgroup.center Q := by
  rw [center_Q]
  exact Subgroup.mem_zpowers zQ

theorem mk_zQ_mul (r : Q) :
    (QuotientGroup.mk (zQ * r) : Q ⧸ Subgroup.center Q) = QuotientGroup.mk r := by
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff zQ).2 zQ_mem_center, one_mul]

theorem classOf_two_eq : Code.classOf (fun _ : Fin 24 => (2 : ℤ)) = twoΩCls := by
  rw [classOf_of_mem' two_omega_mem]
  rfl

theorem toAdd_phi_zw : Multiplicative.toAdd (phi (QuotientGroup.mk (zQ * wQ))) = twoΩCls :=
  (congrArg (fun a => Multiplicative.toAdd (phi a)) (mk_zQ_mul wQ)).trans
    (phi_wQ.trans classOf_two_eq)

theorem modTwoEnd_twoΩCls_eq_iff (p : Pvis) :
    modTwoEnd p.1.2 twoΩCls = twoΩCls ↔
      (conjQ p (zQ * wQ))⁻¹ * (zQ * wQ) ∈ Subgroup.center Q := by
  have h1 : Multiplicative.toAdd (phi (QuotientGroup.mk (conjQ p (zQ * wQ)))) =
      modTwoEnd p.1.2 twoΩCls :=
    (phi_conjQ p (zQ * wQ)).trans (congrArg (modTwoEnd p.1.2) toAdd_phi_zw)
  constructor
  · intro h
    have hmk : (QuotientGroup.mk (conjQ p (zQ * wQ)) : Q ⧸ Subgroup.center Q) =
        QuotientGroup.mk (zQ * wQ) :=
      phi.injective (Multiplicative.toAdd.injective (h1.trans (h.trans toAdd_phi_zw.symm)))
    exact QuotientGroup.eq.1 hmk
  · intro h
    have hmk : (QuotientGroup.mk (conjQ p (zQ * wQ)) : Q ⧸ Subgroup.center Q) =
        QuotientGroup.mk (zQ * wQ) := QuotientGroup.eq.2 h
    exact h1.symm.trans ((congrArg (fun a => Multiplicative.toAdd (phi a)) hmk).trans
      toAdd_phi_zw)

theorem thetaEquiv_conj_xmatTau (p : Pvis) :
    thetaEquiv p * xmatTau * (thetaEquiv p)⁻¹ = rhoEquiv (conjQ p (zQ * wQ)) := by
  rw [xmatTau_eq_rho]
  exact thetaEquiv_conj_rhoEquiv p _

theorem PhiV_mem_Nvis_of_comm
    (g : Gvis)
    (h : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmatTau = xmatTau * g) : PhiV g ∈ Nvis := by
  obtain ⟨p, rfl⟩ := eq_thetaEquiv g
  have h1 : thetaEquiv p * xmatTau * (thetaEquiv p)⁻¹ = xmatTau := by
    have h' : thetaEquiv p * xmatTau = xmatTau * thetaEquiv p := h
    rw [h', mul_inv_cancel_right]
  rw [thetaEquiv_conj_xmatTau, xmatTau_eq_rho] at h1
  have hc : conjQ p (zQ * wQ) = zQ * wQ := rhoEquiv_injective h1
  rw [PhiV_thetaEquiv]
  refine (Hvis_stab_iff _ (PhiV_thetaEquiv p ▸ PhiV_mem_Hvis _)).1 ?_
  rw [modTwoUnit_smul]
  refine (modTwoEnd_twoΩCls_eq_iff p).2 ?_
  rw [hc, inv_mul_cancel]
  exact one_mem _

theorem xmatTau_mem_Qmat :
    xmatTau ∈ Qmat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    CFSG.Monster.Existence.generated_group_Co1_local_recognition_hypotheses
  exact h

theorem xmatTau_ne_one : xmatTau ≠ 1 := by
  rw [xmatTau_eq]
  exact one_ne_yB.symm

theorem xmatTau_ne_xmat : xmatTau ≠ xmat := by
  rw [xmatTau_eq, xmat_eq_xB]
  exact xB_ne_yB.symm

theorem xmat_ne_one : xmat ≠ 1 := by
  rw [xmat_eq_xB]
  exact one_ne_xB.symm

theorem xmat_ne_xmatTau : xmat ≠ xmatTau := xmatTau_ne_xmat.symm

theorem xmat_mul_self : xmat * xmat = 1 := by
  rw [xmat_eq_xB]
  exact xB_mul_self

theorem exists_mul_comm_of_mem_Nvis
    (g : Gvis) (hg : PhiV g ∈ Nvis) :
    ∃ q ∈ Qmat, q * (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmatTau =
      xmatTau * (q * (g : SpaceB ≃ₗ[ℚ] SpaceB)) := by
  obtain ⟨p, rfl⟩ := eq_thetaEquiv g
  have hext := isExtraspecialAmbient_Qmat
  have hxx := xmat_mul_self
  have hstab : modTwoEnd p.1.2 twoΩCls = twoΩCls := by
    have hm : modTwoUnit p.1.2 ∈ Nvis := PhiV_thetaEquiv p ▸ hg
    have := (Hvis_stab_iff _ (Nvis_le_Hvis hm)).2 hm
    rwa [modTwoUnit_smul] at this
  have hcen := (modTwoEnd_twoΩCls_eq_iff p).1 hstab
  rw [center_Q, mem_zpowers_iff_of_orderOf_eq_two orderOf_zQ] at hcen
  have hconj := thetaEquiv_conj_xmatTau p
  rcases hcen with h | h
  · refine ⟨1, one_mem _, ?_⟩
    have hc : conjQ p (zQ * wQ) = zQ * wQ := (inv_mul_eq_one.1 h)
    rw [hc, ← xmatTau_eq_rho] at hconj
    have : thetaEquiv p * xmatTau = xmatTau * thetaEquiv p := by
      rw [mul_inv_eq_iff_eq_mul] at hconj
      exact hconj
    simpa using this
  ·
    have ht := inv_mul_eq_iff_eq_mul.1 h
    have e := (congrArg rhoEquiv ht).trans (rhoEquiv_mul _ _)
    rw [← xmatTau_eq_rho, rhoEquiv_zQ, ← xmat_eq_xB, ← hconj] at e
    have h2 : thetaEquiv p * xmatTau * (thetaEquiv p)⁻¹ = xmat * xmatTau :=
      calc thetaEquiv p * xmatTau * (thetaEquiv p)⁻¹
          = (xmat * xmat) * (thetaEquiv p * xmatTau * (thetaEquiv p)⁻¹) := by rw [hxx, one_mul]
        _ = xmat * (xmat * (thetaEquiv p * xmatTau * (thetaEquiv p)⁻¹)) := mul_assoc _ _ _
        _ = xmat * xmatTau := by rw [← e]
    have h1 : thetaEquiv p * xmatTau = xmat * xmatTau * thetaEquiv p :=
      mul_inv_eq_iff_eq_mul.1 h2
    obtain ⟨q, hq, hqy⟩ : ∃ q ∈ Qmat, q * xmatTau ≠ xmatTau * q := by
      by_contra hcon
      push Not at hcon
      exact (hext.center xmatTau xmatTau_mem_Qmat
        (fun h hh => (hcon h hh).symm)).elim xmatTau_ne_one xmatTau_ne_xmat
    have h2' : q * xmatTau = xmat * (xmatTau * q) :=
      (hext.comm q hq xmatTau xmatTau_mem_Qmat).resolve_left hqy
    have h3 : q * xmat = xmat * q := hext.central q hq
    refine ⟨q, hq, ?_⟩
    calc q * thetaEquiv p * xmatTau = q * (thetaEquiv p * xmatTau) := mul_assoc _ _ _
      _ = q * (xmat * xmatTau * thetaEquiv p) := by rw [h1]
      _ = (q * xmat) * xmatTau * thetaEquiv p := by group
      _ = (xmat * q) * xmatTau * thetaEquiv p := by rw [h3]
      _ = xmat * (q * xmatTau) * thetaEquiv p := by group
      _ = xmat * (xmat * (xmatTau * q)) * thetaEquiv p := by rw [h2']
      _ = (xmat * xmat) * (xmatTau * q) * thetaEquiv p := by group
      _ = xmatTau * (q * thetaEquiv p) := by rw [hxx, one_mul]; group

end CFSG.Monster.Schur
