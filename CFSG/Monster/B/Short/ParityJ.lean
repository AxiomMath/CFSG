module

public import CFSG.Monster.B.Short.AxisAction
public import CFSG.Monster.B.Short.ShortStab
public import CFSG.Monster.Visible.Kernel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.Generated Subgroup

theorem inv_mul_comm_of_mem_centralizer {G : Type*} [Group G] {q r : G}
    (hq : q ∈ centralizer ({r} : Set G)) : q⁻¹ * r = r * q⁻¹ :=
  Commute.inv_left (Subgroup.mem_centralizer_singleton_iff.1 hq : Commute q r)

theorem mem_centralizer_of_mul_comm {G : Type*} [Group G] {q r : G} (h : q * r = r * q) :
    q ∈ centralizer ({r} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 h

theorem rhoEquiv_one : rhoEquiv 1 = 1 :=
  (congrArg thetaEquiv (map_one rhoPair)).trans thetaEquiv_one

theorem rhoEquiv_inv (q : Q) : rhoEquiv q⁻¹ = (rhoEquiv q)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    ((rhoEquiv_mul q q⁻¹).symm.trans ((congrArg rhoEquiv (mul_inv_cancel q)).trans rhoEquiv_one))

@[expose] def rhoHom : Q →* (SpaceB ≃ₗ[ℚ] SpaceB) where
  toFun q := rhoEquiv q⁻¹
  map_one' := (congrArg rhoEquiv inv_one).trans rhoEquiv_one
  map_mul' a b := (congrArg rhoEquiv (mul_inv_rev a b)).trans (rhoEquiv_mul b⁻¹ a⁻¹)

theorem rhoHom_apply (q : Q) : rhoHom q = rhoEquiv q⁻¹ := rfl

theorem rhoHom_injective : Function.Injective rhoHom := fun _ _ h =>
  inv_injective (rhoEquiv_injective h)

theorem rhoHom_of_mul_self {q : Q} (hq : q * q = 1) : rhoHom q = rhoEquiv q :=
  congrArg rhoEquiv (inv_eq_of_mul_eq_one_right hq)

theorem rhoHom_zQ : rhoHom zQ = xmat := rhoHom_of_mul_self zQ_mul_zQ

@[expose] def Jmat (r : Q) : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  (Gmat ⊓ centralizer {xmat}) ⊓ (Gmat ⊓ centralizer {rhoEquiv r})

theorem mem_Jmat_iff {r : Q} {f : SpaceB ≃ₗ[ℚ] SpaceB} :
    f ∈ Jmat r ↔ f ∈ Gvis ∧ f * rhoEquiv r = rhoEquiv r * f := by
  rw [Jmat, Gmat_inf_centralizer_xmat, Subgroup.mem_inf, Subgroup.mem_inf,
    mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hf, -, hc⟩
    exact ⟨hf, hc⟩
  · rintro ⟨hf, hc⟩
    exact ⟨hf, Hmat_le_Gmat hf, hc⟩

theorem Jmat_le_Gvis (r : Q) : Jmat r ≤ Gvis := fun _ hf => (mem_Jmat_iff.1 hf).1

theorem rhoEquiv_mem_Jmat (r : Q) : rhoEquiv r ∈ Jmat r :=
  mem_Jmat_iff.2 ⟨rhoEquiv_mem_Gvis r, rfl⟩

theorem xmat_mem_Jmat (r : Q) : xmat ∈ Jmat r := by
  refine mem_Jmat_iff.2 ⟨rhoEquiv_mem_Gvis zQ, ?_⟩
  have hc : r * zQ = zQ * r := mem_center_iff.1 zQ_mem_center r
  exact (rhoEquiv_mul r zQ).symm.trans ((congrArg rhoEquiv hc).trans (rhoEquiv_mul zQ r))

@[expose] def tJ (r : Q) : Jmat r := ⟨rhoEquiv r, rhoEquiv_mem_Jmat r⟩

@[expose] def xJ (r : Q) : Jmat r := ⟨xmat, xmat_mem_Jmat r⟩

theorem tJ_mem_center (r : Q) : tJ r ∈ center (Jmat r) := by
  rw [mem_center_iff]
  intro f
  exact Subtype.ext (mem_Jmat_iff.1 f.2).2

theorem zpowers_tJ_le_center (r : Q) : zpowers (tJ r) ≤ center (Jmat r) :=
  zpowers_le.2 (tJ_mem_center r)

instance normal_zpowers_tJ (r : Q) : (zpowers (tJ r)).Normal :=
  normal_of_le_center (zpowers_tJ_le_center r)

@[expose] def rhoCent (r : Q) : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := (centralizer {r} : Subgroup Q).map rhoHom

theorem rhoEquiv_mem_rhoCent_iff {r q : Q} : rhoEquiv q ∈ rhoCent r ↔ q ∈ centralizer {r} := by
  constructor
  · rintro ⟨q', hq', hqq'⟩
    have : q'⁻¹ = q := rhoEquiv_injective hqq'
    rw [← this]
    exact inv_mem hq'
  · intro hq
    exact ⟨q⁻¹, inv_mem hq, congrArg rhoEquiv (inv_inv q)⟩

theorem rhoCent_le_Jmat (r : Q) : rhoCent r ≤ Jmat r := by
  intro f hf
  obtain ⟨q, hq, hqf⟩ := Subgroup.mem_map.1 hf
  have hq' : q⁻¹ * r = r * q⁻¹ := inv_mul_comm_of_mem_centralizer hq
  rw [← hqf]
  refine mem_Jmat_iff.2 ⟨rhoEquiv_mem_Gvis _, ?_⟩
  exact (rhoEquiv_mul r q⁻¹).symm.trans ((congrArg rhoEquiv hq'.symm).trans (rhoEquiv_mul q⁻¹ r))

theorem natCard_rhoCent (r : Q) : Nat.card (rhoCent r) = Nat.card (centralizer {r} : Subgroup Q) :=
  (Nat.card_congr (Subgroup.equivMapOfInjective _ rhoHom rhoHom_injective).toEquiv).symm

@[expose] def piJ (r : Q) : Jmat r →* (latticeO ⧸ zpowers negOneO)ᵐᵒᵖ :=
  piVis.comp (Subgroup.inclusion (Jmat_le_Gvis r))

theorem piJ_apply (r : Q) (f : Jmat r) : piJ r f = piVis ⟨f, Jmat_le_Gvis r f.2⟩ := rfl

theorem ker_piJ (r : Q) : (piJ r).ker = (rhoCent r).subgroupOf (Jmat r) := by
  ext f
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, piJ_apply, piVis_eq_one_iff]
  constructor
  · rintro ⟨q, hq⟩
    have hf : (f : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv q := hq.symm
    have hc := (mem_Jmat_iff.1 f.2).2
    rw [hf] at hc
    have hqr : r * q = q * r :=
      rhoEquiv_injective ((rhoEquiv_mul r q).trans (hc.trans (rhoEquiv_mul q r).symm))
    rw [hf]
    exact rhoEquiv_mem_rhoCent_iff.2 (mem_centralizer_of_mul_comm hqr.symm)
  · rintro ⟨q, -, hq⟩
    exact ⟨q⁻¹, hq⟩

instance normal_rhoCent_subgroupOf (r : Q) : ((rhoCent r).subgroupOf (Jmat r)).Normal :=
  ker_piJ r ▸ (piJ r).normal_ker

theorem tJ_mem_rhoCent (r : Q) : tJ r ∈ (rhoCent r).subgroupOf (Jmat r) :=
  rhoEquiv_mem_rhoCent_iff.2 (mem_centralizer_of_mul_comm rfl)

theorem zpowers_tJ_le (r : Q) : zpowers (tJ r) ≤ (rhoCent r).subgroupOf (Jmat r) :=
  zpowers_le.2 (tJ_mem_rhoCent r)

theorem piJ_mem_Kstab (r : Q) (f : Jmat r) : (piJ r f).unop ∈ Kstab (phi0 (coordOf r)) := by
  obtain ⟨p, hp⟩ := mem_Gvis.1 (Jmat_le_Gvis r f.2)
  have hpi : piJ r f = MulOpposite.op (QuotientGroup.mk p.1.2) := by
    rw [piJ_apply]
    exact (congrArg piVis (Subtype.ext hp.symm)).trans (piVis_thetaEquiv p)
  rw [hpi, MulOpposite.unop_op, mk_mem_Kstab_iff]
  have hc := (mem_Jmat_iff.1 f.2).2
  rw [← hp] at hc
  have hconj : conjQ p r = r := by
    apply rhoEquiv_injective
    rw [← thetaEquiv_conj_rhoEquiv, hc, mul_inv_cancel_right]
  calc modTwoEnd p.1.2 (phi0 (coordOf r))
      = modTwoEnd p.1.2 (Multiplicative.toAdd (phi (QuotientGroup.mk r))) :=
        congrArg (modTwoEnd p.1.2) (toAdd_phi_mk r).symm
    _ = Multiplicative.toAdd (phi (QuotientGroup.mk (conjQ p r))) := (phi_conjQ p r).symm
    _ = phi0 (coordOf (conjQ p r)) := toAdd_phi_mk _
    _ = phi0 (coordOf r) := congrArg (fun q => phi0 (coordOf q)) hconj

@[expose] def Equot (r : Q) : Subgroup (Jmat r ⧸ zpowers (tJ r)) :=
  ((rhoCent r).subgroupOf (Jmat r)).map (QuotientGroup.mk' (zpowers (tJ r)))

instance normal_Equot (r : Q) : (Equot r).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

theorem mk_xJ_mem_Equot (r : Q) : (QuotientGroup.mk (xJ r) : Jmat r ⧸ zpowers (tJ r)) ∈ Equot r :=
  ⟨xJ r, rhoEquiv_mem_rhoCent_iff.2 (mem_centralizer_of_mul_comm
    (mem_center_iff.1 zQ_mem_center r).symm), rfl⟩

@[expose] def psiE (r : Q) : invCent r →* Jmat r ⧸ zpowers (tJ r) :=
  (QuotientGroup.mk' (zpowers (tJ r))).comp
    ((rhoHom.comp (invCent r).subtype).codRestrict (Jmat r)
      fun q => rhoCent_le_Jmat r ⟨q, q.2, rfl⟩)

theorem psiE_apply (r : Q) (q : invCent r) :
    psiE r q = QuotientGroup.mk ⟨rhoHom q, rhoCent_le_Jmat r ⟨q, q.2, rfl⟩⟩ := rfl

theorem range_psiE (r : Q) : (psiE r).range = Equot r := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨⟨rhoHom q, rhoCent_le_Jmat r ⟨q, q.2, rfl⟩⟩, ⟨q, q.2, rfl⟩, rfl⟩
  · rintro ⟨f, ⟨q, hq, hqf⟩, rfl⟩
    refine ⟨⟨q, hq⟩, ?_⟩
    rw [psiE_apply]
    exact congrArg QuotientGroup.mk (Subtype.ext hqf)

theorem tJ_mul_self {r : Q} (hr : IsShortCoord (coordOf r)) : tJ r * tJ r = 1 := by
  have hrr : r * r = 1 := by rw [← pow_two]; exact sq_eq_one_of_isShort hr
  apply Subtype.ext
  exact (rhoEquiv_mul r r).symm.trans ((congrArg rhoEquiv hrr).trans rhoEquiv_one)

theorem ne_one_of_isShortCoord {r : Q} (hr : IsShortCoord (coordOf r)) : r ≠ 1 := fun h =>
  not_mem_center_of_isShortCoord hr (by rw [h]; exact one_mem _)

theorem tJ_ne_one {r : Q} (hr : IsShortCoord (coordOf r)) : tJ r ≠ 1 := fun h =>
  ne_one_of_isShortCoord hr
    (rhoEquiv_injective ((congrArg Subtype.val h).trans rhoEquiv_one.symm))

theorem orderOf_of_isShortCoord {r : Q} (hr : IsShortCoord (coordOf r)) : orderOf r = 2 :=
  orderOf_eq_prime (hp := ⟨Nat.prime_two⟩) (sq_eq_one_of_isShort hr) (ne_one_of_isShortCoord hr)

theorem orderOf_tJ {r : Q} (hr : IsShortCoord (coordOf r)) : orderOf (tJ r) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact tJ_mul_self hr) (tJ_ne_one hr)

theorem mem_ker_psiE_iff {r : Q} (q : invCent r) :
    q ∈ (psiE r).ker ↔
      (⟨rhoHom q, rhoCent_le_Jmat r ⟨q, q.2, rfl⟩⟩ : Jmat r) ∈ zpowers (tJ r) :=
  QuotientGroup.eq_one_iff _

theorem ker_psiE {r : Q} (hr : IsShortCoord (coordOf r)) : (psiE r).ker = zpowers (rD r) := by
  have hrr : r * r = 1 := by rw [← pow_two]; exact sq_eq_one_of_isShort hr
  have hr2 : orderOf (rD r) = 2 := orderOf_rD (orderOf_of_isShortCoord hr)
  ext q
  have e1 : (⟨rhoHom q, rhoCent_le_Jmat r ⟨q, q.2, rfl⟩⟩ : Jmat r) = 1 ↔ q = 1 :=
    Subtype.ext_iff.trans ((map_eq_one_iff rhoHom rhoHom_injective).trans OneMemClass.coe_eq_one)
  have e2 : (⟨rhoHom q, rhoCent_le_Jmat r ⟨q, q.2, rfl⟩⟩ : Jmat r) = tJ r ↔ q = rD r := by
    have e : rhoEquiv r = rhoHom r := (rhoHom_of_mul_self hrr).symm
    refine Subtype.ext_iff.trans ?_
    change rhoHom (q : Q) = rhoEquiv r ↔ q = rD r
    rw [e]
    exact rhoHom_injective.eq_iff.trans (Subtype.ext_iff (a1 := q) (a2 := rD r)).symm
  exact (mem_ker_psiE_iff q).trans ((mem_zpowers_iff_of_orderOf_eq_two (orderOf_tJ hr)).trans
    ((or_congr e1 e2).trans (mem_zpowers_iff_of_orderOf_eq_two hr2).symm))

@[expose] def equotEquiv {r : Q} (hr : IsShortCoord (coordOf r)) :
    invCent r ⧸ zpowers (rD r) ≃* Equot r :=
  (QuotientGroup.quotientMulEquivOfEq (ker_psiE hr).symm).trans
    ((QuotientGroup.quotientKerEquivRange (psiE r)).trans (MulEquiv.subgroupCongr (range_psiE r)))

theorem equotEquiv_mk_zD {r : Q} (hr : IsShortCoord (coordOf r)) :
    equotEquiv hr (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers center_Q) r)) =
      ⟨QuotientGroup.mk (xJ r), mk_xJ_mem_Equot r⟩ := by
  apply Subtype.ext
  change psiE r (zD (mem_center_of_center_eq_zpowers center_Q) r) = QuotientGroup.mk (xJ r)
  rw [psiE_apply]
  exact congrArg QuotientGroup.mk (Subtype.ext rhoHom_zQ)

end CFSG.Monster.B.Short
