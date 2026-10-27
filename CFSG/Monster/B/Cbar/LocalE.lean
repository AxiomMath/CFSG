module

public import CFSG.Monster.B.Cbar.LocalAux

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot

@[expose] noncomputable def piKFun (f : Jmat rStar) : Kstab (phi0 (coordOf rStar)) :=
  ⟨(MulOpposite.unop (piJ rStar f))⁻¹, Subgroup.inv_mem _ (piJ_mem_Kstab rStar f)⟩

theorem piKFun_mul (f f' : Jmat rStar) : piKFun (f * f') = piKFun f * piKFun f' := by
  apply Subtype.ext
  change (MulOpposite.unop (piJ rStar (f * f')))⁻¹ =
    (MulOpposite.unop (piJ rStar f))⁻¹ * (MulOpposite.unop (piJ rStar f'))⁻¹
  rw [map_mul, MulOpposite.unop_mul, mul_inv_rev]

@[expose] noncomputable def piK : Jmat rStar →* Kstab (phi0 (coordOf rStar)) :=
  MonoidHom.mk' piKFun piKFun_mul

theorem coe_piK (f : Jmat rStar) :
    ((piK f : Kstab (phi0 (coordOf rStar))) : OLq) = (MulOpposite.unop (piJ rStar f))⁻¹ := rfl

theorem piK_eq_one_iff (f : Jmat rStar) : piK f = 1 ↔ piJ rStar f = 1 := by
  constructor
  · intro h
    have h1 : (MulOpposite.unop (piJ rStar f))⁻¹ = 1 := congrArg Subtype.val h
    rw [inv_eq_one] at h1
    exact MulOpposite.unop_injective (h1.trans MulOpposite.unop_one.symm)
  · intro h
    apply Subtype.ext
    change (MulOpposite.unop (piJ rStar f))⁻¹ = 1
    rw [h, MulOpposite.unop_one, inv_one]

theorem ker_piK : piK.ker = (rhoCent rStar).subgroupOf (Jmat rStar) := by
  ext f
  rw [MonoidHom.mem_ker, piK_eq_one_iff, ← MonoidHom.mem_ker, ker_piJ]

theorem zpowers_tJ_le_ker_piK : Subgroup.zpowers (tJ rStar) ≤ piK.ker := by
  rw [ker_piK]
  exact zpowers_tJ_le rStar

@[expose] noncomputable def piKbar :
    Jmat rStar ⧸ Subgroup.zpowers (tJ rStar) →* Kstab (phi0 (coordOf rStar)) :=
  QuotientGroup.lift _ piK zpowers_tJ_le_ker_piK

theorem ker_piKbar : piKbar.ker = Equot rStar := by
  rw [piKbar, QuotientGroup.ker_lift, ker_piK]
  rfl

@[expose] noncomputable def jbarToKv : Jbar →* Kstab (phi0 (coordOf rStar)) :=
  piKbar.comp jEquiv.symm.toMonoidHom

theorem jbarToKv_jEquiv (y : Jmat rStar ⧸ Subgroup.zpowers (tJ rStar)) :
    jbarToKv (jEquiv y) = piKbar y := by
  change piKbar (jEquiv.symm (jEquiv y)) = piKbar y
  rw [MulEquiv.symm_apply_apply]

theorem jbarToKv_mk (f : Jmat rStar) : jbarToKv (jEquiv (QuotientGroup.mk f)) = piK f :=
  (jbarToKv_jEquiv _).trans rfl

theorem jEmb_jEquiv_symm (j : Jbar) : jEmb (jEquiv.symm j) = (j : Cbar) := by
  change ((jEquiv (jEquiv.symm j) : Jbar) : Cbar) = j
  rw [MulEquiv.apply_symm_apply]

theorem ker_jbarToKv : jbarToKv.ker = Ebar.subgroupOf Jbar := by
  ext j
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h1 : jbarToKv j = 1 ↔ jEquiv.symm j ∈ Equot rStar := by
    rw [← ker_piKbar, MonoidHom.mem_ker]
    exact Iff.rfl
  rw [h1, ← map_Equot_eq_Ebar, ← jEmb_jEquiv_symm j]
  exact (Subgroup.mem_map_iff_mem jEmb_injective).symm

instance Ebar_subgroupOf_normal : (Ebar.subgroupOf Jbar).Normal :=
  ker_jbarToKv ▸ jbarToKv.normal_ker

theorem conj_mem_Ebar {g e : Cbar} (hg : g ∈ Jbar) (he : e ∈ Ebar) : g⁻¹ * e * g ∈ Ebar := by
  have h := Ebar_subgroupOf_normal.conj_mem ⟨e, Ebar_le_Jbar he⟩ he ⟨g, hg⟩⁻¹
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem kappa_mem_Jbar {g₀ : Cgen} (hJ : (g₀ : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar) :
    kappa g₀ ∈ Jbar :=
  ⟨g₀, hJ, rfl⟩

theorem coe_jbarToKv_kappa {g₀ : Cgen} (hJ : (g₀ : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar) {p : Pvis}
    (hp : thetaEquiv p = g₀) :
    ((jbarToKv ⟨kappa g₀, kappa_mem_Jbar hJ⟩ : Kstab (phi0 (coordOf rStar))) : OLq) =
      (QuotientGroup.mk p.1.2)⁻¹ := by
  have hJ' : (g₀ : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jmat rStar := (SetLike.ext_iff.1 Jstar_eq_Jmat _).1 hJ
  have h1 : (⟨kappa g₀, kappa_mem_Jbar hJ⟩ : Jbar) = jEquiv (QuotientGroup.mk ⟨g₀, hJ'⟩) :=
    Subtype.ext rfl
  have h2 : jbarToKv ⟨kappa g₀, kappa_mem_Jbar hJ⟩ = piK ⟨g₀, hJ'⟩ :=
    (congrArg jbarToKv h1).trans (jbarToKv_mk _)
  have hpJ : thetaEquiv p ∈ Jmat rStar := mem_of_eq' hp.symm hJ'
  have h3 : (⟨(g₀ : SpaceB ≃ₗ[ℚ] SpaceB), hJ'⟩ : Jmat rStar) = ⟨thetaEquiv p, hpJ⟩ :=
    Subtype.ext hp.symm
  have h4 : piJ rStar ⟨thetaEquiv p, hpJ⟩ = MulOpposite.op (QuotientGroup.mk p.1.2) :=
    piVis_thetaEquiv p
  calc ((jbarToKv ⟨kappa g₀, kappa_mem_Jbar hJ⟩ : Kstab (phi0 (coordOf rStar))) : OLq)
      = ((piK ⟨g₀, hJ'⟩ : Kstab (phi0 (coordOf rStar))) : OLq) := congrArg Subtype.val h2
    _ = (MulOpposite.unop (piJ rStar ⟨g₀, hJ'⟩))⁻¹ := rfl
    _ = (MulOpposite.unop (piJ rStar ⟨thetaEquiv p, hpJ⟩))⁻¹ :=
        congrArg (fun f => (MulOpposite.unop (piJ rStar f))⁻¹) h3
    _ = (QuotientGroup.mk p.1.2)⁻¹ := congrArg (fun x => (MulOpposite.unop x)⁻¹) h4

theorem tStar_mul_xmat : tStar * xmat = rhoEquiv (zQ * rStar) := by
  rw [rhoEquiv_mul]
  rfl

theorem rStar_mul_self : rStar * rStar = 1 := by
  have := sq_eq_one_of_isShort isShortCoord_rStar
  rwa [pow_two] at this

theorem eq_of_mul_eq_one' {G : Type*} [Group G] {a b : G} (hb : b * b = 1) (h : a * b = 1) :
    a = b := by
  calc a = a * b * b := by rw [mul_assoc, hb, mul_one]
    _ = b := by rw [h, one_mul]

theorem eq_mul_of_mul_eq' {G : Type*} [Group G] {a b c : G} (hb : b * b = 1) (h : a * b = c) :
    a = c * b := by
  calc a = a * b * b := by rw [mul_assoc, hb, mul_one]
    _ = c * b := by rw [h]

theorem mul_mul_cancel' {G : Type*} [Group G] {b c : G} (hb : b * b = 1) : c * b * b = c := by
  rw [mul_assoc, hb, mul_one]

theorem mem_centralizer_of_map {G : Type*} [Group G] (f : G ≃* G) {r q : G} (hr : f r = r)
    (hq : q ∈ Subgroup.centralizer {r}) : f q ∈ Subgroup.centralizer {r} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hq ⊢
  calc f q * r = f q * f r := by rw [hr]
    _ = f (q * r) := (map_mul f q r).symm
    _ = f (r * q) := by rw [hq]
    _ = f r * f q := map_mul f r q
    _ = r * f q := by rw [hr]

theorem phi0_coordOf_inv (q : Q) : phi0 (coordOf q⁻¹) = phi0 (coordOf q) := by
  rw [← toAdd_phiQ, ← toAdd_phiQ, map_inv, toAdd_inv]
  exact ZModModule.neg_eq_self _

theorem phi0_coordOf_eq_zero_iff (q : Q) : phi0 (coordOf q) = 0 ↔ q = 1 ∨ q = zQ := by
  rw [← toAdd_phiQ, toAdd_eq_zero]
  change phi (QuotientGroup.mk q) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, center_Q]
  exact Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_zQ

theorem phi0_coordOf_eq_v_iff (q : Q) :
    phi0 (coordOf q) = phi0 (coordOf rStar) ↔ q = rStar ∨ q = zQ * rStar := by
  have h1 : phi0 (coordOf q) = phi0 (coordOf rStar) ↔ phi0 (coordOf (q * rStar)) = 0 := by
    rw [phi0_coordOf_mul, ← ZModModule.sub_eq_add, sub_eq_zero]
  rw [h1, phi0_coordOf_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact .inl (eq_of_mul_eq_one' (G := Q) rStar_mul_self h)
    · exact .inr (eq_mul_of_mul_eq' (G := Q) rStar_mul_self h)
  · rintro (rfl | rfl)
    · exact .inl rStar_mul_self
    · exact .inr (mul_mul_cancel' (G := Q) rStar_mul_self)

theorem phi0_conjQ (p : Pvis) (q : Q) :
    phi0 (coordOf (conjQ p q)) = modTwoEnd p.1.2 (phi0 (coordOf q)) :=
  ((toAdd_phi_mk _).symm.trans (phi_conjQ p q)).trans
    (congrArg (modTwoEnd p.1.2) (toAdd_phi_mk q))

theorem kappa_rho_eq_one_iff {q : Q} (hq : rhoEquiv q ∈ Cgen) :
    kappa ⟨rhoEquiv q, hq⟩ = 1 ↔ q = 1 ∨ q = rStar := by
  rw [kappa_eq_one_iff]
  constructor
  · rintro (h | h)
    · exact .inl (rhoEquiv_injective ((congrArg Subtype.val h).trans rhoEquiv_one'.symm))
    · exact .inr (rhoEquiv_injective (congrArg Subtype.val h))
  · rintro (rfl | rfl)
    · exact .inl (Subtype.ext rhoEquiv_one')
    · exact .inr rfl

theorem kappa_rho_eq_xbar_iff {q : Q} (hq : rhoEquiv q ∈ Cgen) :
    kappa ⟨rhoEquiv q, hq⟩ = xbar ↔ q = zQ ∨ q = zQ * rStar := by
  have h1 : kappa ⟨rhoEquiv q, hq⟩ = xbar ↔ kappa (⟨rhoEquiv q, hq⟩ * xC⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    rfl
  rw [h1, kappa_eq_one_iff]
  constructor
  · rintro (h | h)
    · have h2 : rhoEquiv q * xmat⁻¹ = 1 := congrArg Subtype.val h
      exact .inl (rhoEquiv_injective (mul_inv_eq_one.1 h2))
    · have h2 : rhoEquiv q * xmat⁻¹ = tStar := congrArg Subtype.val h
      exact .inr (rhoEquiv_injective ((mul_inv_eq_iff_eq_mul.1 h2).trans tStar_mul_xmat))
  · rintro (rfl | rfl)
    · exact .inl (Subtype.ext (mul_inv_cancel xmat))
    · refine .inr (Subtype.ext ?_)
      change rhoEquiv (zQ * rStar) * xmat⁻¹ = tStar
      exact (congrArg (· * xmat⁻¹) tStar_mul_xmat.symm).trans (mul_inv_cancel_right tStar xmat)

@[expose] noncomputable def psiQ :
    invCent rStar ⧸ Subgroup.zpowers (rD rStar) →* Multiplicative (Wv (phi0 (coordOf rStar))) :=
  QuotientGroup.lift _ (psi0 rfl) (Subgroup.zpowers_le.2 (psi0_rD rfl))

@[expose] noncomputable def psiBar : Ebar →* Multiplicative (Wv (phi0 (coordOf rStar))) :=
  psiQ.comp ((equotEquiv isShortCoord_rStar).symm.toMonoidHom.comp eEquiv.symm.toMonoidHom)

theorem coe_eEquiv_equotEquiv_mk (q : invCent rStar) :
    ((eEquiv (equotEquiv isShortCoord_rStar (QuotientGroup.mk q)) : Ebar) : Cbar) =
      kappa ⟨rhoHom q, Jmat_le_Cgen (rhoCent_le_Jmat rStar ⟨q, q.2, rfl⟩)⟩ := rfl

theorem psiBar_eEquiv (y : Equot rStar) :
    psiBar (eEquiv y) = psiQ ((equotEquiv isShortCoord_rStar).symm y) :=
  congrArg (fun z => psiQ ((equotEquiv isShortCoord_rStar).symm z))
    (MulEquiv.symm_apply_apply eEquiv y)

theorem psiBar_eEquiv_equotEquiv_mk (q : invCent rStar) :
    psiBar (eEquiv (equotEquiv isShortCoord_rStar (QuotientGroup.mk q))) = psi0 rfl q :=
  (psiBar_eEquiv _).trans
    (congrArg psiQ (MulEquiv.symm_apply_apply (equotEquiv isShortCoord_rStar) _))

theorem psiBar_kappa_rho {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) :
    psiBar ⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩, kappa_rho_mem_Ebar hq⟩ =
      Multiplicative.ofAdd (Submodule.Quotient.mk ⟨phi0 (coordOf q), phi0_mem_vPerpL rfl hq⟩) := by
  have hq' : q⁻¹ ∈ invCent rStar := Subgroup.inv_mem _ hq
  have h1 : (⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩, kappa_rho_mem_Ebar hq⟩ : Ebar) =
      eEquiv (equotEquiv isShortCoord_rStar (QuotientGroup.mk ⟨q⁻¹, hq'⟩)) := by
    apply Subtype.ext
    refine Eq.trans ?_ (coe_eEquiv_equotEquiv_mk ⟨q⁻¹, hq'⟩).symm
    refine congrArg kappa (Subtype.ext ?_)
    change rhoEquiv q = rhoHom q⁻¹
    rw [rhoHom_apply, inv_inv]
  calc psiBar ⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩, kappa_rho_mem_Ebar hq⟩
      = psiBar (eEquiv (equotEquiv isShortCoord_rStar (QuotientGroup.mk ⟨q⁻¹, hq'⟩))) :=
        congrArg psiBar h1
    _ = psi0 rfl ⟨q⁻¹, hq'⟩ := psiBar_eEquiv_equotEquiv_mk _
    _ = Multiplicative.ofAdd (Submodule.Quotient.mk
          ⟨phi0 (coordOf q⁻¹), phi0_mem_vPerpL rfl hq'⟩) := psi0_apply rfl _
    _ = Multiplicative.ofAdd (Submodule.Quotient.mk ⟨phi0 (coordOf q), phi0_mem_vPerpL rfl hq⟩) :=
        congrArg (fun z : vPerpL (phi0 (coordOf rStar)) =>
          Multiplicative.ofAdd (Submodule.Quotient.mk z : Wv (phi0 (coordOf rStar))))
          (Subtype.ext (phi0_coordOf_inv q))

theorem psiQ_surjective : Function.Surjective psiQ :=
  QuotientGroup.lift_surjective_of_surjective _ _ (psi0_surjective rfl) _

theorem psiBar_surjective : Function.Surjective psiBar :=
  psiQ_surjective.comp
    ((equotEquiv isShortCoord_rStar).symm.surjective.comp eEquiv.symm.surjective)

theorem exists_rep_Ebar (e : Ebar) :
    ∃ q, ∃ hq : q ∈ Subgroup.centralizer {rStar},
      e = ⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩, kappa_rho_mem_Ebar hq⟩ := by
  obtain ⟨g, hg, he⟩ := e.2
  obtain ⟨q, hq, hqg⟩ := mem_rhoCQ.1 (Subgroup.mem_subgroupOf.1 hg)
  exact ⟨q, hq, Subtype.ext (he.symm.trans (congrArg kappa (Subtype.ext hqg.symm)))⟩

theorem psiBar_eq_one_iff (e : Ebar) : psiBar e = 1 ↔ e = 1 ∨ e = ⟨xbar, xbar_mem_Ebar⟩ := by
  obtain ⟨q, hq, rfl⟩ := exists_rep_Ebar e
  rw [psiBar_kappa_rho hq, ofAdd_eq_one, Submodule.Quotient.mk_eq_zero]
  have h1 : (⟨phi0 (coordOf q), phi0_mem_vPerpL rfl hq⟩ : vPerpL (phi0 (coordOf rStar))) ∈
      vLineInL (phi0 (coordOf rStar)) ↔
        phi0 (coordOf q) = 0 ∨ phi0 (coordOf q) = phi0 (coordOf rStar) := mem_vLineL
  have h2 : (⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩, kappa_rho_mem_Ebar hq⟩ : Ebar) = 1 ↔
      kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ = 1 := Subtype.ext_iff
  have h3 : (⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩, kappa_rho_mem_Ebar hq⟩ : Ebar) =
      ⟨xbar, xbar_mem_Ebar⟩ ↔ kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ = xbar := Subtype.ext_iff
  rw [h1, h2, h3, phi0_coordOf_eq_zero_iff, phi0_coordOf_eq_v_iff, kappa_rho_eq_one_iff,
    kappa_rho_eq_xbar_iff]
  exact or_or_or_comm

theorem inv_conj_eq_of_eq {G : Type*} [Group G] {a b x y : G} (h : a = b)
    (hx : a⁻¹ * x * a⁻¹⁻¹ = y) : b⁻¹ * x * b = y := by
  subst h
  rwa [inv_inv] at hx

theorem conjQ_rStar_of_mem_Jstar {p : Pvis} (hp : thetaEquiv p ∈ Jstar) :
    conjQ p rStar = rStar := by
  have hc : thetaEquiv p * tStar = tStar * thetaEquiv p :=
    Subgroup.mem_centralizer_singleton_iff.1 hp.2
  have h1 := Short.thetaEquiv_conj_rhoEquiv p rStar
  have h2 : thetaEquiv p * rhoEquiv rStar * (thetaEquiv p)⁻¹ = rhoEquiv rStar :=
    (congrArg (· * (thetaEquiv p)⁻¹) hc).trans (mul_inv_cancel_right tStar (thetaEquiv p))
  exact rhoEquiv_injective (h1.symm.trans h2)

theorem conjQ_mem_centralizer {p : Pvis} (hp : conjQ p rStar = rStar) {q : Q}
    (hq : q ∈ Subgroup.centralizer {rStar}) : conjQ p q ∈ Subgroup.centralizer {rStar} :=
  mem_centralizer_of_map (conjQ p) hp hq

theorem psiBar_conj {g e : Cbar} (hg : g ∈ Jbar) (he : e ∈ Ebar) :
    psiBar ⟨g⁻¹ * e * g, conj_mem_Ebar hg he⟩ =
      Multiplicative.ofAdd (wAct _ (jbarToKv ⟨g, hg⟩) (Multiplicative.toAdd (psiBar ⟨e, he⟩))) := by
  obtain ⟨g₀, hg₀, hgg⟩ := hg
  subst hgg
  obtain ⟨q, hq, hqe⟩ := exists_rep_Ebar ⟨e, he⟩
  have hqe' : e = kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ := congrArg Subtype.val hqe
  subst hqe'
  have hJ : (g₀ : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar := hg₀
  obtain ⟨p, hp⟩ := mem_Gvis.1 hJ.1
  have hpJ : thetaEquiv p ∈ Jstar := mem_of_eq' hp.symm hJ
  have hp'J : thetaEquiv p⁻¹ ∈ Jstar := mem_of_eq' (thetaEquiv_inv p).symm (Jstar.inv_mem hpJ)
  have hq' : conjQ p⁻¹ q ∈ Subgroup.centralizer {rStar} :=
    conjQ_mem_centralizer (conjQ_rStar_of_mem_Jstar hp'J) hq
  have h2 : (g₀ : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * rhoEquiv q * (g₀ : SpaceB ≃ₗ[ℚ] SpaceB) =
      rhoEquiv (conjQ p⁻¹ q) :=
    inv_conj_eq_of_eq hp (conj_eq_of_eq' (thetaEquiv_inv p) (Short.thetaEquiv_conj_rhoEquiv p⁻¹ q))
  have h3 : g₀⁻¹ * ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ * g₀ =
      (⟨rhoEquiv (conjQ p⁻¹ q), rhoEquiv_mem_Cgen hq'⟩ : Cgen) := Subtype.ext h2
  have h4 : (kappa g₀)⁻¹ * kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ * kappa g₀ =
      kappa ⟨rhoEquiv (conjQ p⁻¹ q), rhoEquiv_mem_Cgen hq'⟩ := by
    have h5 : kappa (g₀⁻¹ * ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ * g₀) =
        (kappa g₀)⁻¹ * kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ * kappa g₀ := by
      rw [map_mul, map_mul, map_inv]
    exact h5.symm.trans (congrArg kappa h3)
  have hk := coe_jbarToKv_kappa hJ hp
  have h7 : phi0 (coordOf (conjQ p⁻¹ q)) =
      kOp ((jbarToKv ⟨kappa g₀, kappa_mem_Jbar hJ⟩ : Kstab (phi0 (coordOf rStar))) : OLq)
        (phi0 (coordOf q)) := by
    rw [hk, phi0_conjQ]
    rfl
  calc psiBar ⟨(kappa g₀)⁻¹ * kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ * kappa g₀, _⟩
      = psiBar ⟨kappa ⟨rhoEquiv (conjQ p⁻¹ q), rhoEquiv_mem_Cgen hq'⟩, kappa_rho_mem_Ebar hq'⟩ :=
        congrArg psiBar (Subtype.ext h4)
    _ = Multiplicative.ofAdd (Submodule.Quotient.mk
          ⟨phi0 (coordOf (conjQ p⁻¹ q)), phi0_mem_vPerpL rfl hq'⟩) := psiBar_kappa_rho hq'
    _ = Multiplicative.ofAdd (wAct _ (jbarToKv ⟨kappa g₀, kappa_mem_Jbar hJ⟩)
          (Submodule.Quotient.mk ⟨phi0 (coordOf q), phi0_mem_vPerpL rfl hq⟩)) :=
        congrArg (fun z : vPerpL (phi0 (coordOf rStar)) =>
          Multiplicative.ofAdd (Submodule.Quotient.mk z : Wv (phi0 (coordOf rStar))))
          (Subtype.ext h7)
    _ = Multiplicative.ofAdd (wAct _ (jbarToKv ⟨kappa g₀, kappa_mem_Jbar hJ⟩)
          (Multiplicative.toAdd (psiBar ⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩,
            kappa_rho_mem_Ebar hq⟩))) := by
        rw [psiBar_kappa_rho hq, toAdd_ofAdd]

theorem mem_Ebar_of_conj_trivial {g : Cbar} (hg : g ∈ Jbar)
    (h : ∀ (e : Cbar) (he : e ∈ Ebar), psiBar ⟨g⁻¹ * e * g, conj_mem_Ebar hg he⟩ = psiBar ⟨e, he⟩) :
    g ∈ Ebar := by
  have hw : wAct _ (jbarToKv ⟨g, hg⟩) = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨e, he⟩ := psiBar_surjective (Multiplicative.ofAdd w)
    have h1 := (psiBar_conj hg e.2).symm.trans (h e e.2)
    have h2 : psiBar ⟨(e : Cbar), e.2⟩ = Multiplicative.ofAdd w := he
    rw [h2, toAdd_ofAdd] at h1
    exact Multiplicative.ofAdd.injective h1
  have hk : jbarToKv ⟨g, hg⟩ = 1 := by
    apply KvAct_injective_rStar
    rw [map_one]
    exact congrArg MulOpposite.op hw
  have hmem : (⟨g, hg⟩ : Jbar) ∈ Ebar.subgroupOf Jbar := by
    rw [← ker_jbarToKv]
    exact hk
  exact hmem

end CFSG.Monster.B
