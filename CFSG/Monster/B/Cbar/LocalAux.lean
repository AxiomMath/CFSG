module

public import CFSG.Monster.B.Cbar.JbarIso

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot

open scoped commutatorElement

theorem spinEquiv_s_eq_one_iff (s : ZMod 2) : spinEquiv (⟨s, 0, 0⟩ : SpinCoord) = 1 ↔ s = 0 := by
  constructor
  · intro h
    have h1 : (⟨s, 0, 0⟩ : SpinCoord) = 1 := spinEquiv.injective (h.trans (map_one _).symm)
    exact congrArg SpinCoord.s h1
  · intro h
    rw [h]
    exact map_one spinEquiv

theorem commute_iff_bL (q r : Q) :
    q * r = r * q ↔ bL (phi0 (coordOf q)) (phi0 (coordOf r)) = 0 := by
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have h1 : ⁅q, r⁆ = spinEquiv ⁅spinEquiv.symm q, spinEquiv.symm r⁆ := by
    rw [map_commutatorElement, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rw [h1, SpinCoord.commutatorElement_eq, spinEquiv_s_eq_one_iff]
  exact (bL_phi0 _ _ _ _).symm ▸ Iff.rfl

variable {r : Q} {v : L2}

theorem mem_centralizer_iff_bL (r q : Q) :
    q ∈ Subgroup.centralizer {r} ↔ bL (phi0 (coordOf r)) (phi0 (coordOf q)) = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff, eq_comm, commute_iff_bL, bL_comm]

theorem phi0_mem_vPerpL (hv : phi0 (coordOf r) = v) {q : Q} (hq : q ∈ Subgroup.centralizer {r}) :
    phi0 (coordOf q) ∈ vPerpL v := by
  have h := (mem_centralizer_iff_bL r q).1 hq
  rw [hv] at h
  exact h

@[expose] noncomputable def phiQ : Q →* Multiplicative L2 :=
  phi.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))

theorem toAdd_phiQ (q : Q) : Multiplicative.toAdd (phiQ q) = phi0 (coordOf q) := toAdd_phi_mk q

theorem phiQ_surjective : Function.Surjective phiQ :=
  phi.surjective.comp (QuotientGroup.mk'_surjective _)

theorem phi0_coordOf_mul (q q' : Q) :
    phi0 (coordOf (q * q')) = phi0 (coordOf q) + phi0 (coordOf q') := by
  rw [← toAdd_phiQ, ← toAdd_phiQ, ← toAdd_phiQ, map_mul, toAdd_mul]

theorem exists_mem_centralizer_phi0 (hv : phi0 (coordOf r) = v) {x : L2} (hx : x ∈ vPerpL v) :
    ∃ q ∈ Subgroup.centralizer {r}, phi0 (coordOf q) = x := by
  obtain ⟨q, hq⟩ := phiQ_surjective (Multiplicative.ofAdd x)
  have hqx : phi0 (coordOf q) = x := by
    rw [← toAdd_phiQ, hq, toAdd_ofAdd]
  refine ⟨q, (mem_centralizer_iff_bL r q).2 ?_, hqx⟩
  rw [hqx, hv]
  exact hx

theorem self_mem_vLineL (v : L2) : v ∈ vLineL v := by
  rw [vLineL]
  exact Submodule.mem_span_singleton_self _

theorem self_mem_vPerpL (v : L2) : v ∈ vPerpL v := vLineL_le_vPerpL v (self_mem_vLineL v)

theorem self_mem_vLineInL (v : L2) : (⟨v, self_mem_vPerpL v⟩ : vPerpL v) ∈ vLineInL v :=
  self_mem_vLineL v

theorem coordOf_one' : coordOf (1 : Q) = 0 := by
  rw [coordOf, map_one]
  rfl

@[expose] noncomputable def psi0Fun (hv : phi0 (coordOf r) = v) (q : invCent r) :
    Multiplicative (Wv v) :=
  Multiplicative.ofAdd (Submodule.Quotient.mk ⟨phi0 (coordOf (q : Q)), phi0_mem_vPerpL hv q.2⟩)

theorem psi0Fun_mul (hv : phi0 (coordOf r) = v) (q q' : invCent r) :
    psi0Fun hv (q * q') = psi0Fun hv q * psi0Fun hv q' := by
  have h : (⟨phi0 (coordOf ((q * q' : invCent r) : Q)), phi0_mem_vPerpL hv (q * q').2⟩ :
      vPerpL v) = ⟨phi0 (coordOf (q : Q)), phi0_mem_vPerpL hv q.2⟩ +
        ⟨phi0 (coordOf (q' : Q)), phi0_mem_vPerpL hv q'.2⟩ :=
    Subtype.ext (phi0_coordOf_mul (q : Q) q')
  unfold psi0Fun
  rw [h, Submodule.Quotient.mk_add, ofAdd_add]

@[expose] noncomputable def psi0 (hv : phi0 (coordOf r) = v) : invCent r →* Multiplicative (Wv v) :=
  MonoidHom.mk' (psi0Fun hv) (psi0Fun_mul hv)

theorem psi0_apply (hv : phi0 (coordOf r) = v) (q : invCent r) :
    psi0 hv q = Multiplicative.ofAdd (Submodule.Quotient.mk ⟨phi0 (coordOf (q : Q)),
      phi0_mem_vPerpL hv q.2⟩) := rfl

theorem psi0_surjective (hv : phi0 (coordOf r) = v) : Function.Surjective (psi0 hv) := by
  intro y
  have hy : ∃ x, Submodule.Quotient.mk x = Multiplicative.toAdd y :=
    Submodule.Quotient.mk_surjective (vLineInL v) _
  obtain ⟨x, hx⟩ := hy
  obtain ⟨q, hq, hqx⟩ := exists_mem_centralizer_phi0 hv x.2
  refine ⟨⟨q, hq⟩, ?_⟩
  have e : (⟨phi0 (coordOf q), phi0_mem_vPerpL hv hq⟩ : vPerpL v) = x := Subtype.ext hqx
  have h1 : psi0 hv ⟨q, hq⟩ = Multiplicative.ofAdd (Submodule.Quotient.mk
      (⟨phi0 (coordOf q), phi0_mem_vPerpL hv hq⟩ : vPerpL v)) := psi0_apply hv ⟨q, hq⟩
  calc psi0 hv ⟨q, hq⟩ = Multiplicative.ofAdd (Submodule.Quotient.mk
        (⟨phi0 (coordOf q), phi0_mem_vPerpL hv hq⟩ : vPerpL v)) := h1
    _ = Multiplicative.ofAdd (Submodule.Quotient.mk x : Wv v) :=
        congrArg (fun z : vPerpL v => Multiplicative.ofAdd (Submodule.Quotient.mk z : Wv v)) e
    _ = Multiplicative.ofAdd (Multiplicative.toAdd y) := congrArg Multiplicative.ofAdd hx
    _ = y := ofAdd_toAdd y

theorem psi0_eq_one_iff (hv : phi0 (coordOf r) = v) (q : invCent r) :
    psi0 hv q = 1 ↔ phi0 (coordOf (q : Q)) = 0 ∨ phi0 (coordOf (q : Q)) = v := by
  rw [psi0_apply, ofAdd_eq_one, Submodule.Quotient.mk_eq_zero]
  exact mem_vLineL

theorem psi0_rD (hv : phi0 (coordOf r) = v) : psi0 hv (rD r) = 1 := (psi0_eq_one_iff hv _).2 (.inr hv)

theorem wAct_eq_one_of {k : OLq} (hk : k ∈ Kstab v)
    (h : ∀ x : L2, x ∈ vPerpL v → kOp k x = x ∨ kOp k x = x + v) :
    wAct v ⟨k, hk⟩ = 1 := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [wAct_mk, Module.End.one_apply, Submodule.Quotient.eq]
    rcases h x x.2 with h1 | h1
    · have : (⟨kOp k x, kOp_mem_vPerpL hk x.2⟩ : vPerpL v) - x = 0 :=
        sub_eq_zero.2 (Subtype.ext h1)
      rw [this]
      exact zero_mem _
    · have : (⟨kOp k x, kOp_mem_vPerpL hk x.2⟩ : vPerpL v) - x = ⟨v, self_mem_vPerpL v⟩ :=
        Subtype.ext (show kOp k (x : L2) - (x : L2) = v by rw [h1]; exact add_sub_cancel_left _ _)
      rw [this]
      exact self_mem_vLineInL v

theorem mem_rhoCent_of_conj (hv : phi0 (coordOf r) = v) (hinj : Function.Injective (KvAct v))
    {p : Pvis} (hJ : thetaEquiv p ∈ Jmat r)
    (h : ∀ q ∈ Subgroup.centralizer {r}, conjQ p q = q ∨ conjQ p q = q * r) :
    thetaEquiv p ∈ rhoCent r := by
  have hpi : piJ r ⟨thetaEquiv p, hJ⟩ = MulOpposite.op (QuotientGroup.mk p.1.2) :=
    piVis_thetaEquiv p
  have hk : (QuotientGroup.mk p.1.2 : OLq) ∈ Kstab v := by
    have := piJ_mem_Kstab r ⟨thetaEquiv p, hJ⟩
    rw [hpi, MulOpposite.unop_op, hv] at this
    exact this
  have hw : wAct v ⟨QuotientGroup.mk p.1.2, hk⟩ = 1 := by
    refine wAct_eq_one_of hk fun x hx => ?_
    obtain ⟨q, hq, rfl⟩ := exists_mem_centralizer_phi0 hv hx
    rw [kOp_mk]
    have e1 : modTwoEnd p.1.2 (phi0 (coordOf q)) = phi0 (coordOf (conjQ p q)) :=
      (congrArg (modTwoEnd p.1.2) (toAdd_phi_mk q)).symm.trans
        ((phi_conjQ p q).symm.trans (toAdd_phi_mk _))
    rw [e1]
    rcases h q hq with h1 | h1
    · exact .inl (by rw [h1])
    · exact .inr (by rw [h1, phi0_coordOf_mul, hv])
  have hk1 : (⟨QuotientGroup.mk p.1.2, hk⟩ : Kstab v) = 1 := by
    apply hinj
    rw [map_one]
    exact congrArg MulOpposite.op hw
  have hpi1 : piJ r ⟨thetaEquiv p, hJ⟩ = 1 := by
    rw [hpi]
    have : (QuotientGroup.mk p.1.2 : OLq) = 1 := congrArg Subtype.val hk1
    rw [this, MulOpposite.op_one]
  have hker : (⟨thetaEquiv p, hJ⟩ : Jmat r) ∈ (piJ r).ker := hpi1
  rw [ker_piJ] at hker
  exact hker

theorem orderOf_tStarC : orderOf tStarC = 2 := by
  have h := orderOf_injective Cgen.subtype Subtype.coe_injective tStarC
  rw [Subgroup.coe_subtype] at h
  rw [← h]
  exact orderOf_tStar

theorem kappa_eq_one_iff (g : Cgen) : kappa g = 1 ↔ g = 1 ∨ g = tStarC := by
  rw [← MonoidHom.mem_ker, ker_kappa, Zstar]
  exact Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_tStarC

theorem mem_of_eq' {G : Type*} [Group G] {S : Subgroup G} {a b : G} (h : a = b) (ha : a ∈ S) :
    b ∈ S :=
  h ▸ ha

theorem conj_eq_of_eq' {G : Type*} [Group G] {a b x y : G} (h : a = b)
    (hx : a * x * a⁻¹ = y) : b * x * b⁻¹ = y :=
  h ▸ hx

theorem KvAct_injective_rStar : Function.Injective (KvAct (phi0 (coordOf rStar))) :=
  phi0_coordOf_rStar ▸ KvAct_injective_vMinus

theorem rhoEquiv_mem_Cgen {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) : rhoEquiv q ∈ Cgen :=
  rhoCQ_le_Cgen (mem_rhoCQ.2 ⟨q, hq, rfl⟩)

theorem kappa_rho_mem_Ebar {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) :
    kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ ∈ Ebar :=
  ⟨⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩, mem_rhoCQ.2 ⟨q, hq, rfl⟩, rfl⟩

theorem mem_rhoCQ_of_commute_Ebar {g : Cgen} (hg : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar)
    (hc : ∀ e ∈ Ebar, e * kappa g = kappa g * e) : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoCQ := by
  obtain ⟨p, hp⟩ := mem_Gvis.1 hg.1
  have hJ : thetaEquiv p ∈ Jmat rStar :=
    mem_of_eq' hp.symm ((SetLike.ext_iff.1 Jstar_eq_Jmat _).1 hg)
  have hconj : ∀ q ∈ Subgroup.centralizer {rStar}, conjQ p q = q ∨ conjQ p q = q * rStar := by
    intro q hq
    have hc' := hc _ (kappa_rho_mem_Ebar hq)
    have h1 : kappa (g * ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ * g⁻¹ *
        (⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ : Cgen)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc']
      group
    have hge : (g : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ =
        rhoEquiv (conjQ p q) := conj_eq_of_eq' hp (Short.thetaEquiv_conj_rhoEquiv p q)
    rcases (kappa_eq_one_iff _).1 h1 with h2 | h2
    · left
      have h3 : (g : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
          (rhoEquiv q)⁻¹ = 1 := congrArg Subtype.val h2
      exact rhoEquiv_injective (hge.symm.trans (mul_inv_eq_one.1 h3))
    · right
      have h3 : (g : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
          (rhoEquiv q)⁻¹ = tStar := congrArg Subtype.val h2
      have h4 : rhoEquiv (conjQ p q) = rhoEquiv rStar * rhoEquiv q :=
        hge.symm.trans (mul_inv_eq_iff_eq_mul.1 h3)
      exact rhoEquiv_injective (h4.trans (rhoEquiv_mul q rStar).symm)
  have hmem := mem_rhoCent_of_conj rfl KvAct_injective_rStar hJ hconj
  exact mem_of_eq' hp ((SetLike.ext_iff.1 rhoCent_eq_rhoCQ _).1 hmem)

end CFSG.Monster.B
