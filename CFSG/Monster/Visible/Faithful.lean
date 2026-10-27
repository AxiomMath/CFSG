module

public import CFSG.Monster.Visible.Kernel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel Matrix
open scoped IsMulCommutative

abbrev rhoQvis : Subgroup Gvis := rhoQ.subgroupOf Gvis

@[expose] def rhoN (r : Q) : rhoQvis :=
  ⟨⟨rhoEquiv r, rhoEquiv_mem_Gvis r⟩, Subgroup.mem_subgroupOf.2 (rhoEquiv_mem_rhoQ r)⟩

theorem coe_coe_rhoN (r : Q) : ((rhoN r : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv r := rfl

theorem rhoN_mul (r r' : Q) : rhoN (r * r') = rhoN r' * rhoN r :=
  Subtype.ext (Subtype.ext (rhoEquiv_mul r r'))

theorem rhoN_one : rhoN 1 = 1 :=
  Subtype.ext (Subtype.ext ((congrArg thetaEquiv (map_one rhoPair)).trans thetaEquiv_one))

theorem rhoN_injective : Function.Injective rhoN := fun _ _ h =>
  rhoEquiv_injective (congrArg (fun x : rhoQvis => ((x : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)) h)

theorem rhoN_surjective : Function.Surjective rhoN := by
  intro x
  obtain ⟨r, hr⟩ := mem_rhoQ.1 (Subgroup.mem_subgroupOf.1 x.2)
  exact ⟨r, Subtype.ext (Subtype.ext hr)⟩

@[expose] def rhoHom : Q →* (rhoQvis)ᵐᵒᵖ where
  toFun r := MulOpposite.op (rhoN r)
  map_one' := congrArg MulOpposite.op rhoN_one
  map_mul' r r' := congrArg MulOpposite.op (rhoN_mul r r')

@[expose] def rhoIso : Q ≃* (rhoQvis)ᵐᵒᵖ :=
  MulEquiv.ofBijective rhoHom ⟨fun _ _ h => rhoN_injective (MulOpposite.op_injective h),
    fun x => ⟨(rhoN_surjective x.unop).choose,
      congrArg MulOpposite.op (rhoN_surjective x.unop).choose_spec⟩⟩

theorem rhoIso_apply (r : Q) : rhoIso r = MulOpposite.op (rhoN r) := rfl

theorem rhoN_zpow (r : Q) (k : ℤ) : rhoN (r ^ k) = rhoN r ^ k :=
  MulOpposite.op_injective ((map_zpow rhoIso r k).trans (MulOpposite.op_zpow (rhoN r) k).symm)

@[expose] def zRho : Subgroup rhoQvis := Subgroup.zpowers (rhoN zQ)

theorem coe_coe_rhoN_zQ : ((rhoN zQ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = xB := rhoEquiv_zQ

theorem rhoN_mem_zRho_iff (u : Q) : rhoN u ∈ zRho ↔ u ∈ Subgroup.zpowers zQ := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [← rhoN_zpow] at hk
    rw [← rhoN_injective hk]
    exact Subgroup.zpow_mem_zpowers zQ k
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [rhoN_zpow]
    exact Subgroup.zpow_mem_zpowers _ k

@[expose] def projRho : rhoQvis →* Multiplicative (C × Cocode) where
  toFun x := projQ (rhoIso.symm (MulOpposite.op x))
  map_one' := (congrArg projQ (map_one rhoIso.symm)).trans (map_one projQ)
  map_mul' x y := (congrArg projQ (map_mul rhoIso.symm (MulOpposite.op y) (MulOpposite.op x))).trans
    ((map_mul projQ _ _).trans (mul_comm _ _))

theorem projRho_rhoN (r : Q) : projRho (rhoN r) = projQ r :=
  congrArg projQ (rhoIso.symm_apply_apply r)

theorem ker_projRho : projRho.ker = zRho := by
  ext x
  obtain ⟨r, rfl⟩ := rhoN_surjective x
  rw [MonoidHom.mem_ker, projRho_rhoN, rhoN_mem_zRho_iff, ← center_Q, ← ker_projQ,
    MonoidHom.mem_ker]

theorem projRho_surjective : Function.Surjective projRho := fun v => by
  obtain ⟨r, hr⟩ := projQ_surjective v
  exact ⟨rhoN r, (projRho_rhoN r).trans hr⟩

instance normal_zRho : zRho.Normal := ker_projRho ▸ projRho.normal_ker

abbrev VisMod : Type := rhoQvis ⧸ zRho

@[expose] def visModEquiv : VisMod ≃* Multiplicative (C × Cocode) :=
  (QuotientGroup.quotientMulEquivOfEq ker_projRho.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective projRho projRho_surjective)

theorem visModEquiv_mk (r : Q) : visModEquiv (QuotientGroup.mk (rhoN r)) = projQ r :=
  projRho_rhoN r

@[expose] def visModEquivQuot : VisMod ≃* Q ⧸ Subgroup.center Q :=
  visModEquiv.trans quotCenterEquiv.symm

theorem visModEquivQuot_mk (r : Q) :
    visModEquivQuot (QuotientGroup.mk (rhoN r)) = QuotientGroup.mk r :=
  quotCenterEquiv.symm_apply_eq.2 (visModEquiv_mk r)

instance isElementaryAbelian_visMod : IsElementaryAbelian 2 VisMod :=
  isElementaryAbelian_two_of_mulEquiv visModEquiv

theorem natCard_visMod : Nat.card VisMod = 2 ^ 24 := by
  rw [Nat.card_congr visModEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
    natCard_C, natCard_cocode]
  norm_num

@[expose] def visModLinearEquiv : Additive VisMod ≃ₗ[ZMod 2] C × Cocode :=
  (MulEquiv.toAdditiveLeft visModEquiv).toLinearEquiv fun c x => ZMod.map_smul _ c x

theorem finrank_visMod : Module.finrank (ZMod 2) (Additive VisMod) = 24 :=
  visModLinearEquiv.finrank_eq.trans finrank_C_prod_cocode

theorem thetaEquiv_conj_rhoEquiv (p : Pvis) (t : Q) :
    thetaEquiv p * rhoEquiv t * (thetaEquiv p)⁻¹ = rhoEquiv (conjQ p t) := by
  have hpair : p⁻¹ * rhoPair t * p = rhoPair (conjQ p t) :=
    Subtype.ext (Prod.ext rfl (by
      show p.1.2⁻¹ * 1 * p.1.2 = 1
      rw [mul_one, inv_mul_cancel]))
  rw [← thetaEquiv_inv]
  show thetaEquiv p * thetaEquiv (rhoPair t) * thetaEquiv p⁻¹ = thetaEquiv (rhoPair (conjQ p t))
  rw [← hpair, thetaEquiv_mul (p⁻¹ * rhoPair t) p, thetaEquiv_mul p⁻¹ (rhoPair t), mul_assoc]

theorem conjNormal_thetaEquiv_rhoN (p : Pvis) (t : Q) :
    MulAut.conjNormal (⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ : Gvis) (rhoN t) =
      rhoN (conjQ p t) :=
  Subtype.ext (Subtype.ext (thetaEquiv_conj_rhoEquiv p t))

theorem eq_thetaEquiv (g : Gvis) : ∃ p : Pvis, g = ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ := by
  obtain ⟨p, hp⟩ := mem_Gvis.1 g.2
  exact ⟨p, Subtype.ext hp.symm⟩

theorem conjNormal_rhoN_zQ (g : Gvis) : MulAut.conjNormal g (rhoN zQ) = rhoN zQ := by
  obtain ⟨p, rfl⟩ := eq_thetaEquiv g
  exact (conjNormal_thetaEquiv_rhoN p zQ).trans (congrArg rhoN (conjQ_zQ p))

theorem map_conjNormal_zRho (g : Gvis) :
    zRho.map (MulAut.conjNormal g : rhoQvis ≃* rhoQvis).toMonoidHom = zRho :=
  ((MulAut.conjNormal g : rhoQvis ≃* rhoQvis).toMonoidHom.map_zpowers (rhoN zQ)).trans
    (congrArg Subgroup.zpowers (conjNormal_rhoN_zQ g))

@[expose] def conjVis : Gvis →* MulAut VisMod where
  toFun g := QuotientGroup.congr zRho zRho (MulAut.conjNormal g) (map_conjNormal_zRho g)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (by rw [map_one]; rfl)
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (by rw [map_mul]; rfl)

theorem conjVis_mk (g : Gvis) (x : rhoQvis) :
    conjVis g (QuotientGroup.mk x) = QuotientGroup.mk (MulAut.conjNormal g x) := rfl

theorem conjVis_thetaEquiv_mk (p : Pvis) (t : Q) :
    conjVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ (QuotientGroup.mk (rhoN t)) =
      QuotientGroup.mk (rhoN (conjQ p t)) :=
  congrArg QuotientGroup.mk (conjNormal_thetaEquiv_rhoN p t)

theorem mk_rhoN_eq_iff (t t' : Q) :
    (QuotientGroup.mk (rhoN t) : VisMod) = QuotientGroup.mk (rhoN t') ↔
      coordOf t = coordOf t' := by
  rw [QuotientGroup.eq, ← ker_projRho, MonoidHom.mem_ker, map_mul projRho, map_inv projRho,
    projRho_rhoN, projRho_rhoN, inv_mul_eq_one, coordOf_eq_iff_projQ]

theorem conjVis_eq_one_iff (g : Gvis) :
    conjVis g = 1 ↔ ∀ x : rhoQvis,
      (QuotientGroup.mk (MulAut.conjNormal g x) : VisMod) = QuotientGroup.mk x := by
  constructor
  · intro h x
    exact (conjVis_mk g x).symm.trans (DFunLike.congr_fun h (QuotientGroup.mk x))
  · intro h
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with
    | H x => exact (conjVis_mk g x).trans (h x)

theorem conjVis_thetaEquiv_eq_one_iff (p : Pvis) :
    conjVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ = 1 ↔ modTwoEnd p.1.2 = 1 := by
  rw [conjVis_eq_one_iff]
  constructor
  · intro h
    have hc : ∀ t : Q, coordOf (conjQ p t) = coordOf t := fun t =>
      (mk_rhoN_eq_iff _ _).1
        ((congrArg QuotientGroup.mk (conjNormal_thetaEquiv_rhoN p t)).symm.trans (h (rhoN t)))
    refine LinearMap.ext fun v => ?_
    obtain ⟨c, hcv⟩ := phi.surjective (Multiplicative.ofAdd v)
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective c
    have e : v = Multiplicative.toAdd (phi (QuotientGroup.mk t)) :=
      congrArg Multiplicative.toAdd hcv.symm
    subst e
    exact (phi_conjQ p t).symm.trans ((toAdd_phi_mk (conjQ p t)).trans
      ((congrArg phi0 (hc t)).trans (toAdd_phi_mk t).symm))
  · intro h x
    obtain ⟨t, rfl⟩ := rhoN_surjective x
    have hc : coordOf (conjQ p t) = coordOf t := phi0_injective
      ((toAdd_phi_mk (conjQ p t)).symm.trans ((phi_conjQ p t).trans
        ((LinearMap.congr_fun h _).trans (toAdd_phi_mk t))))
    exact (congrArg QuotientGroup.mk (conjNormal_thetaEquiv_rhoN p t)).trans
      ((mk_rhoN_eq_iff _ _).2 hc)

theorem conjVis_eq_one_iff_piVis (g : Gvis) : conjVis g = 1 ↔ piVis g = 1 := by
  obtain ⟨p, rfl⟩ := eq_thetaEquiv g
  rw [conjVis_thetaEquiv_eq_one_iff, piVis_thetaEquiv p, MulOpposite.op_eq_one_iff,
    QuotientGroup.eq_one_iff, zpowers_negOneO_eq_ker, mem_ker_modTwoHom]

theorem ker_conjVis : conjVis.ker = rhoQvis := by
  refine Eq.trans ?_ ker_piVis
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, conjVis_eq_one_iff_piVis]

@[expose] def autLinear (a : MulAut VisMod) : Additive VisMod ≃ₗ[ZMod 2] Additive VisMod :=
  (MulEquiv.toAdditive a).toLinearEquiv fun c x => ZMod.map_smul (MulEquiv.toAdditive a) c x

@[expose] def autToGL :
    MulAut VisMod →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod) where
  toFun a := LinearMap.GeneralLinearGroup.ofLinearEquiv (autLinear a)
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => rfl)

theorem autToGL_apply (a : MulAut VisMod) (x : VisMod) :
    ((autToGL a : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
      Additive VisMod →ₗ[ZMod 2] Additive VisMod) (Additive.ofMul x) = Additive.ofMul (a x) :=
  rfl

theorem autToGL_injective : Function.Injective autToGL := fun _ _ h =>
  MulEquiv.ext fun x => Additive.ofMul.injective
    (congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod) =>
      (f : Additive VisMod →ₗ[ZMod 2] Additive VisMod) (Additive.ofMul x)) h)

@[expose] def repVis : Gvis →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod) :=
  autToGL.comp conjVis

theorem repVis_apply (g : Gvis) (x : rhoQvis) :
    ((repVis g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
      Additive VisMod →ₗ[ZMod 2] Additive VisMod) (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g x)) :=
  rfl

theorem ker_repVis : repVis.ker = rhoQvis := by
  rw [repVis, MonoidHom.ker_comp_of_injective _ _ autToGL_injective, ker_conjVis]

@[expose] def repQuot :
    Gvis ⧸ rhoQvis →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod) :=
  QuotientGroup.lift rhoQvis repVis ker_repVis.ge

theorem repQuot_mk (g : Gvis) : repQuot (QuotientGroup.mk g) = repVis g := rfl

theorem repQuot_injective : Function.Injective repQuot :=
  (QuotientGroup.injective_lift_iff _ _ _).2 ker_repVis.symm

theorem visible_quotient_faithful_action :
    rhoQvis.Normal ∧
    (∀ x : Gvis, x ∈ rhoQvis ↔ ∃ r : Q, rhoEquiv r = x) ∧
    (∀ r : Q, ((rhoN r : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv r) ∧
    zRho = Subgroup.zpowers (rhoN zQ) ∧ ((rhoN zQ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = xB ∧
    (∀ r : Q, visModEquivQuot (QuotientGroup.mk (rhoN r)) = QuotientGroup.mk r) ∧
    (∀ (g : Gvis) (x : rhoQvis), conjVis g (QuotientGroup.mk x) =
      QuotientGroup.mk (MulAut.conjNormal g x) ∧
      ((MulAut.conjNormal g x : rhoQvis) : Gvis) = g * x * g⁻¹) ∧
    (∀ (p : Pvis) (t : Q), conjVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩
      (QuotientGroup.mk (rhoN t)) = QuotientGroup.mk (rhoN (conjQ p t))) ∧
    conjVis.ker = rhoQvis ∧
    (∀ (g : Gvis) (x : rhoQvis),
      ((repVis g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
        Additive VisMod →ₗ[ZMod 2] Additive VisMod) (Additive.ofMul (QuotientGroup.mk x)) =
        Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g x))) ∧
    repVis.ker = rhoQvis ∧
    (∀ g : Gvis, repQuot (QuotientGroup.mk g) = repVis g) ∧
    Function.Injective repQuot ∧
    IsElementaryAbelian 2 VisMod ∧ Nat.card VisMod = 2 ^ 24 ∧
    Module.finrank (ZMod 2) (Additive VisMod) = 24 :=
  ⟨normal_rhoQ_subgroupOf, fun _ => Subgroup.mem_subgroupOf.trans mem_rhoQ, coe_coe_rhoN, rfl,
    coe_coe_rhoN_zQ, visModEquivQuot_mk, fun g x => ⟨conjVis_mk g x, MulAut.conjNormal_apply g x⟩,
    conjVis_thetaEquiv_mk, ker_conjVis, repVis_apply, ker_repVis, repQuot_mk, repQuot_injective,
    isElementaryAbelian_visMod, natCard_visMod, finrank_visMod⟩

end CFSG.Monster.Visible
