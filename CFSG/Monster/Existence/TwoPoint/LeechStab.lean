module

public import CFSG.Monster.Existence.TwoPoint.LeechForm
public import CFSG.Monster.B.Short.ParityCentralizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Generated CFSG.Monster.B.Short CFSG.Monster.B Subgroup
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem leech_exists_zpow_of_eq_or_eq {z r s : G} (h : s = r ∨ s = z * r) :
    ∃ e : ZMod 2, s = z ^ e.val * r := by
  rcases h with h | h
  · exact ⟨0, by rw [h, ZMod.val_zero, pow_zero, one_mul]⟩
  · exact ⟨1, by rw [h, ZMod.val_one, pow_one]⟩

theorem leech_inv_mul_mul_eq_zpow_of {z r q : G} {b : ZMod 2} (hz : z ∈ center G)
    (hc : ⁅r, q⁆ = 1 ∨ ⁅r, q⁆ = z) (hb : r * q = q * r ↔ b = 0) :
    q⁻¹ * r * q = z ^ b.val * r := by
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) b with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, one_mul]
    have h' : r * q = q * r := hb.2 rfl
    rw [mul_assoc, h', inv_mul_cancel_left]
  · rw [ZMod.val_one, pow_one]
    have hne : ¬ r * q = q * r := fun h' => one_ne_zero (hb.1 h')
    rcases hc with h2 | h2
    · exact absurd (commutatorElement_eq_one_iff_mul_comm.1 h2) hne
    · exact conj_eq_mul_of_commutatorElement hz h2

theorem leech_zpow_mul_zpow_mul_cancel {z : G} (hzz : z * z = 1) (n : ℕ) (r : G) :
    z ^ n * (z ^ n * r) = r := by
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, pow_two, hzz, one_pow, one_mul]

theorem leech_inv_mul_comm_of_comm {q r : G} (h : q * r = r * q) : q⁻¹ * r = r * q⁻¹ :=
  (Commute.inv_left (show Commute q r from h)).eq

theorem leech_apply_eq_of_zpow {z : G} (_hz : z ∈ center G) (hzz : z * z = 1) (n : ℕ) (F : G → G)
    {r x : G} (hx : x = z ^ n * r) (hF : F (z ^ n * r) = z ^ n * F r) (hFr : F r = z ^ n * r) :
    F x = r := by
  rw [hx, hF, hFr, leech_zpow_mul_zpow_mul_cancel hzz]

end Generic

theorem leech_inv_mul_mul_eq_zpow_bL (r q : Q) :
    q⁻¹ * r * q = zQ ^ (bL (phi0 (coordOf r)) (phi0 (coordOf q))).val * r :=
  leech_inv_mul_mul_eq_zpow_of Short.zQ_mem_center
    (commutatorElement_eq_one_or_eq isExtraspecialPGroup_Q center_Q r q) (commute_iff_bL r q)

theorem exists_conjQ_eq_two {r₁ r₂ : Q} (h₁ : phi0 (coordOf r₁) ≠ 0) (h₂ : phi0 (coordOf r₂) ≠ 0)
    (h₁₂ : phi0 (coordOf r₁) ≠ phi0 (coordOf r₂)) (p : Pvis)
    (hp₁ : modTwoEnd p.1.2 (phi0 (coordOf r₁)) = phi0 (coordOf r₁))
    (hp₂ : modTwoEnd p.1.2 (phi0 (coordOf r₂)) = phi0 (coordOf r₂)) :
    ∃ p' : Pvis, conjQ p' r₁ = r₁ ∧ conjQ p' r₂ = r₂ ∧ p'.1.2 = p.1.2 := by
  have key : ∀ r : Q, modTwoEnd p.1.2 (phi0 (coordOf r)) = phi0 (coordOf r) →
      ∃ e : ZMod 2, conjQ p r = zQ ^ e.val * r := fun r hr =>
    leech_exists_zpow_of_eq_or_eq (eq_or_eq_zQ_mul_of_coordOf_eq
      (phi0_injective ((phi0_conjQ p r).trans hr)))
  refine (key r₁ hp₁).elim fun e₁ he₁ => (key r₂ hp₂).elim fun e₂ he₂ =>
    (leech_exists_dual h₁ h₂ h₁₂ e₁ e₂).elim fun y hy =>
    (phiQ_surjective (Multiplicative.ofAdd y)).elim fun q hq => ?_
  have hqy : phi0 (coordOf q) = y := by rw [← toAdd_phiQ, hq, toAdd_ofAdd]
  have step : ∀ (r : Q) (e : ZMod 2), conjQ p r = zQ ^ e.val * r →
      bL (phi0 (coordOf r)) y = e → conjQ (p * rhoPair q) r = r := fun r e he hb => by
    have h5 : q⁻¹ * r * q = zQ ^ e.val * r :=
      (leech_inv_mul_mul_eq_zpow_bL r q).trans (congrArg (fun b : ZMod 2 => zQ ^ b.val * r)
        ((congrArg (bL (phi0 (coordOf r))) hqy).trans hb))
    exact (conjQ_mul p (rhoPair q) r).trans (leech_apply_eq_of_zpow Short.zQ_mem_center zQ_mul_zQ
      e.val (conjQ (rhoPair q)) he (conjQ_zQ_pow_mul (rhoPair q) e.val r)
      ((conjQ_rhoPair q r).trans h5))
  refine ⟨p * rhoPair q, step r₁ e₁ he₁ hy.1, step r₂ e₂ he₂ hy.2, ?_⟩
  show p.1.2 * 1 = p.1.2
  rw [mul_one]

@[expose] def leechJ (r₁ r₂ : Q) : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  Gvis ⊓ centralizer {rhoEquiv r₁} ⊓ centralizer {rhoEquiv r₂}

theorem mem_leechJ_iff {r₁ r₂ : Q} {f : SpaceB ≃ₗ[ℚ] SpaceB} :
    f ∈ leechJ r₁ r₂ ↔
      f ∈ Gvis ∧ f * rhoEquiv r₁ = rhoEquiv r₁ * f ∧ f * rhoEquiv r₂ = rhoEquiv r₂ * f := by
  rw [leechJ, mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    and_assoc]

theorem leechJ_le_Gvis (r₁ r₂ : Q) : leechJ r₁ r₂ ≤ Gvis := fun _ hf => (mem_leechJ_iff.1 hf).1

theorem leechJ_le_Jmat_left (r₁ r₂ : Q) : leechJ r₁ r₂ ≤ Jmat r₁ := fun _ hf =>
  mem_Jmat_iff.2 ⟨(mem_leechJ_iff.1 hf).1, (mem_leechJ_iff.1 hf).2.1⟩

theorem leechJ_le_Jmat_right (r₁ r₂ : Q) : leechJ r₁ r₂ ≤ Jmat r₂ := fun _ hf =>
  mem_Jmat_iff.2 ⟨(mem_leechJ_iff.1 hf).1, (mem_leechJ_iff.1 hf).2.2⟩

theorem thetaEquiv_comm_rhoEquiv_iff (p : Pvis) (r : Q) :
    thetaEquiv p * rhoEquiv r = rhoEquiv r * thetaEquiv p ↔ conjQ p r = r := by
  have h := thetaEquiv_conj_rhoEquiv p r
  constructor
  · intro hc
    apply rhoEquiv_injective
    rw [← h, hc, mul_inv_cancel_right]
  · intro hc
    rw [hc] at h
    exact mul_inv_eq_iff_eq_mul.1 h

theorem conjQ_eq_of_thetaEquiv_mem_leechJ {r₁ r₂ : Q} {p : Pvis}
    (hp : thetaEquiv p ∈ leechJ r₁ r₂) : conjQ p r₁ = r₁ ∧ conjQ p r₂ = r₂ :=
  ⟨(thetaEquiv_comm_rhoEquiv_iff p r₁).1 (mem_leechJ_iff.1 hp).2.1,
    (thetaEquiv_comm_rhoEquiv_iff p r₂).1 (mem_leechJ_iff.1 hp).2.2⟩

theorem thetaEquiv_mem_leechJ_iff {r₁ r₂ : Q} (p : Pvis) :
    thetaEquiv p ∈ leechJ r₁ r₂ ↔ conjQ p r₁ = r₁ ∧ conjQ p r₂ = r₂ :=
  ⟨conjQ_eq_of_thetaEquiv_mem_leechJ, fun h => mem_leechJ_iff.2 ⟨thetaEquiv_mem_Gvis p,
    (thetaEquiv_comm_rhoEquiv_iff p r₁).2 h.1, (thetaEquiv_comm_rhoEquiv_iff p r₂).2 h.2⟩⟩

@[expose] def piLeech (r₁ r₂ : Q) : leechJ r₁ r₂ →* (latticeO ⧸ zpowers negOneO)ᵐᵒᵖ :=
  piVis.comp (Subgroup.inclusion (leechJ_le_Gvis r₁ r₂))

theorem piLeech_apply (r₁ r₂ : Q) (f : leechJ r₁ r₂) :
    piLeech r₁ r₂ f = piVis ⟨f, leechJ_le_Gvis r₁ r₂ f.2⟩ := rfl

theorem rhoEquiv_mem_map_rhoHom_iff {M : Subgroup Q} {q : Q} :
    rhoEquiv q ∈ M.map rhoHom ↔ q ∈ M := by
  constructor
  · rintro ⟨q', hq', hqq'⟩
    have : q'⁻¹ = q := rhoEquiv_injective hqq'
    rw [← this]
    exact inv_mem hq'
  · intro hq
    exact ⟨q⁻¹, inv_mem hq, congrArg rhoEquiv (inv_inv q)⟩

abbrev leechC (r₁ r₂ : Q) : Subgroup Q := centralizer {r₁} ⊓ centralizer {r₂}

theorem mem_leechC_iff {r₁ r₂ q : Q} : q ∈ leechC r₁ r₂ ↔ q * r₁ = r₁ * q ∧ q * r₂ = r₂ * q :=
  mem_inf.trans (and_congr mem_centralizer_singleton_iff mem_centralizer_singleton_iff)

theorem map_rhoHom_le_leechJ {r₁ r₂ : Q} {M : Subgroup Q} (hM : M ≤ leechC r₁ r₂) :
    M.map rhoHom ≤ leechJ r₁ r₂ := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨h1, h2⟩ := mem_leechC_iff.1 (hM hq)
  have key : ∀ r : Q, q * r = r * q → rhoHom q * rhoEquiv r = rhoEquiv r * rhoHom q := by
    intro r h
    have h' : q⁻¹ * r = r * q⁻¹ := leech_inv_mul_comm_of_comm h
    exact (rhoEquiv_mul r q⁻¹).symm.trans ((congrArg rhoEquiv h'.symm).trans (rhoEquiv_mul q⁻¹ r))
  exact mem_leechJ_iff.2 ⟨rhoEquiv_mem_Gvis _, key r₁ h1, key r₂ h2⟩

theorem ker_piLeech (r₁ r₂ : Q) :
    (piLeech r₁ r₂).ker = ((leechC r₁ r₂).map rhoHom).subgroupOf (leechJ r₁ r₂) := by
  ext f
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, piLeech_apply, piVis_eq_one_iff]
  constructor
  · rintro ⟨q, hq⟩
    have hf : (f : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv q := hq.symm
    obtain ⟨-, hc1, hc2⟩ := mem_leechJ_iff.1 f.2
    rw [hf] at hc1 hc2
    have key : ∀ r : Q, rhoEquiv q * rhoEquiv r = rhoEquiv r * rhoEquiv q → r * q = q * r :=
      fun r hc => rhoEquiv_injective ((rhoEquiv_mul r q).trans (hc.trans (rhoEquiv_mul q r).symm))
    rw [hf]
    exact rhoEquiv_mem_map_rhoHom_iff.2 (mem_leechC_iff.2 ⟨(key r₁ hc1).symm, (key r₂ hc2).symm⟩)
  · rintro ⟨q, -, hq⟩
    exact ⟨q⁻¹, hq⟩

instance normal_ker_leechC (r₁ r₂ : Q) :
    (((leechC r₁ r₂).map rhoHom).subgroupOf (leechJ r₁ r₂)).Normal :=
  ker_piLeech r₁ r₂ ▸ (piLeech r₁ r₂).normal_ker

@[expose] def leechRhoEquiv {r₁ r₂ : Q} {M : Subgroup Q} (hM : M ≤ leechC r₁ r₂) :
    (M.map rhoHom).subgroupOf (leechJ r₁ r₂) ≃* M :=
  (Subgroup.subgroupOfEquivOfLe (map_rhoHom_le_leechJ hM)).trans
    (M.equivMapOfInjective rhoHom rhoHom_injective).symm

@[expose] def leechNEquiv (r₁ r₂ : Q) :
    ((leechC r₁ r₂).map rhoHom).subgroupOf (leechJ r₁ r₂) ≃* leechC r₁ r₂ :=
  leechRhoEquiv le_rfl

theorem piLeech_mem_Kstab_left (r₁ r₂ : Q) (f : leechJ r₁ r₂) :
    (piLeech r₁ r₂ f).unop ∈ Kstab (phi0 (coordOf r₁)) :=
  piJ_mem_Kstab r₁ ⟨f, leechJ_le_Jmat_left r₁ r₂ f.2⟩

theorem piLeech_mem_Kstab_right (r₁ r₂ : Q) (f : leechJ r₁ r₂) :
    (piLeech r₁ r₂ f).unop ∈ Kstab (phi0 (coordOf r₂)) :=
  piJ_mem_Kstab r₂ ⟨f, leechJ_le_Jmat_right r₁ r₂ f.2⟩

theorem range_piLeech
    {r₁ r₂ : Q} (h₁ : phi0 (coordOf r₁) ≠ 0) (h₂ : phi0 (coordOf r₂) ≠ 0)
    (h₁₂ : phi0 (coordOf r₁) ≠ phi0 (coordOf r₂)) :
    (piLeech r₁ r₂).range = (Kstab (phi0 (coordOf r₁)) ⊓ Kstab (phi0 (coordOf r₂))).op := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact mem_inf.2 ⟨piLeech_mem_Kstab_left r₁ r₂ f, piLeech_mem_Kstab_right r₁ r₂ f⟩
  · intro x hx
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.unop
    have hk : (QuotientGroup.mk g : OLq) ∈ Kstab (phi0 (coordOf r₁)) ⊓ Kstab (phi0 (coordOf r₂)) :=
      hg ▸ hx
    obtain ⟨s, hs⟩ := exists_mem_Pvis g
    obtain ⟨p', hp'₁, hp'₂, hp'g⟩ := exists_conjQ_eq_two h₁ h₂ h₁₂ ⟨(s, g), hs⟩
      (mk_mem_Kstab_iff _ _ |>.1 hk.1) (mk_mem_Kstab_iff _ _ |>.1 hk.2)
    have hJ : thetaEquiv p' ∈ leechJ r₁ r₂ := (thetaEquiv_mem_leechJ_iff p').2 ⟨hp'₁, hp'₂⟩
    refine ⟨⟨thetaEquiv p', hJ⟩, ?_⟩
    rw [piLeech_apply]
    refine (piVis_thetaEquiv p').trans ?_
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_op, hp'g, hg]

@[expose] def leechQuotEquiv
    {r₁ r₂ : Q} (h₁ : phi0 (coordOf r₁) ≠ 0)
    (h₂ : phi0 (coordOf r₂) ≠ 0) (h₁₂ : phi0 (coordOf r₁) ≠ phi0 (coordOf r₂)) :
    leechJ r₁ r₂ ⧸ ((leechC r₁ r₂).map rhoHom).subgroupOf (leechJ r₁ r₂) ≃*
      ↥(Kstab (phi0 (coordOf r₁)) ⊓ Kstab (phi0 (coordOf r₂))) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_piLeech r₁ r₂).symm).trans
    ((QuotientGroup.quotientKerEquivRange (piLeech r₁ r₂)).trans
      ((MulEquiv.subgroupCongr (range_piLeech h₁ h₂ h₁₂)).trans (opSubgroupEquiv _)))

theorem normal_leechRho {r₁ r₂ : Q} {M : Subgroup Q}
    (hM : ∀ p : Pvis, thetaEquiv p ∈ leechJ r₁ r₂ → ∀ t ∈ M, conjQ p t ∈ M) :
    ((M.map rhoHom).subgroupOf (leechJ r₁ r₂)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : SpaceB ≃ₗ[ℚ] SpaceB) ∈ M.map rhoHom := hn
  refine (hn'.elim fun t ht => ?_ : (((g * n * g⁻¹ : leechJ r₁ r₂)) : SpaceB ≃ₗ[ℚ] SpaceB) ∈
    M.map rhoHom)
  refine (mem_Gvis.1 (leechJ_le_Gvis r₁ r₂ g.2)).elim fun p hp => ?_
  have hpJ : thetaEquiv p ∈ leechJ r₁ r₂ := hp ▸ g.2
  have e1 : (n : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv t⁻¹ := ht.2.symm
  have e2 : rhoEquiv (conjQ p t⁻¹) =
      (g : SpaceB ≃ₗ[ℚ] SpaceB) * (n : SpaceB ≃ₗ[ℚ] SpaceB) * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := by
    rw [← thetaEquiv_conj_rhoEquiv p t⁻¹, hp, e1]
  exact ⟨conjQ p t, hM p hpJ t ht.1, (rhoHom_apply _).trans
    ((congrArg rhoEquiv (map_inv (conjQ p) t).symm).trans e2)⟩

end CFSG.Monster.Existence
