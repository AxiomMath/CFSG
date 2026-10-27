
module

public import CFSG.Monster.B.TwoA.Triality.PermMain
public import CFSG.Monster.B.TwoA.Base.FourNormBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Lifts CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.ScalarKernel
  CFSG.Monster.B.Short CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.B.Co2

attribute [local instance] vAction

theorem Ctwo_le_Jhat : Ctwo ≤ Jhat := by
  intro g hg
  rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_centralizer_iff.1 hg) xhat xhat_mem_Vhat).symm

theorem Ctwo_le_Ptwo :
    Ctwo ≤ Ptwo := fun _ hg => ⟨Ctwo_le_Jhat hg, Ctwo_le_Ntwo hg⟩

theorem jhatToKv_mem_monoSub
    {g : Dfull} (hg : g ∈ Ptwo) :
    ((jhatToKv ⟨g, Ptwo_le_Jhat hg⟩ : Kstab (phi0 (coordOf rStar))) : OLq) ∈ monoSub ceqHyp := by
  have h : (⟨g, Ptwo_le_Jhat hg⟩ : Jhat) ∈ Ptwo.subgroupOf Jhat := hg
  rw [Ptwo_eq_comap, Subgroup.mem_comap, Subgroup.mem_subgroupOf] at h
  exact h

@[expose] def piPFun
    (g : Ptwo) : Mfr :=
  ⟨⟨_, monoSub_ceq_le_Kstab (jhatToKv_mem_monoSub g.2)⟩,
    (mem_Mfr_iff _).2 (jhatToKv_mem_monoSub g.2)⟩

@[expose] def piP :
    Ptwo →* Mfr where
  toFun := piPFun
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change ((jhatToKv 1 : Kstab (phi0 (coordOf rStar))) : OLq) = 1
    rw [map_one]
    rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change ((jhatToKv (⟨(a : Dfull), Ptwo_le_Jhat a.2⟩ * ⟨(b : Dfull), Ptwo_le_Jhat b.2⟩) :
      Kstab (phi0 (coordOf rStar))) : OLq) = _
    rw [map_mul]
    rfl

theorem coe_piP
    (g : Ptwo) :
    (((piP g : Mfr) : Kstab v0) : OLq) =
      ((jhatToKv ⟨g, Ptwo_le_Jhat g.2⟩ : Kstab (phi0 (coordOf rStar))) : OLq) := rfl

@[expose] def piC :
    Ctwo →* Mfr := piP.comp (Subgroup.inclusion Ctwo_le_Ptwo)

theorem coe_piC
    (g : Ctwo) :
    (((piC g : Mfr) : Kstab v0) : OLq) =
      ((jhatToKv ⟨g, Ctwo_le_Jhat g.2⟩ : Kstab (phi0 (coordOf rStar))) : OLq) := rfl

@[expose] def projP :

    Mfr →* Ppair := SemidirectProduct.rightHom.comp MfrEquiv.symm.toMonoidHom

theorem projP_surjective :
    Function.Surjective projP :=
  SemidirectProduct.rightHom_surjective.comp MfrEquiv.symm.surjective

theorem projP_MfrEquiv
    (x : SDD ceqHyp) : projP (MfrEquiv x) = x.right := by
  change SemidirectProduct.rightHom (MfrEquiv.symm (MfrEquiv x)) = x.right
  rw [MulEquiv.symm_apply_apply]
  rfl

@[expose] def Aeq :

    Subgroup Mfr := (SemidirectProduct.inl.range).map MfrEquiv.toMonoidHom

theorem Aeq_eq_ker :
    Aeq = projP.ker := by
  ext m
  obtain ⟨x, rfl⟩ := MfrEquiv.surjective m
  rw [MonoidHom.mem_ker, projP_MfrEquiv, ← SemidirectProduct.rightHom_eq_right,
    ← MonoidHom.mem_ker, ← SemidirectProduct.range_inl_eq_ker_rightHom, Aeq,
    Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem natCard_Aeq :
    Nat.card Aeq = 2 ^ 10 := by
  rw [Aeq, ← Nat.card_congr ((SemidirectProduct.inl.range).equivMapOfInjective
    MfrEquiv.toMonoidHom MfrEquiv.injective).toEquiv, ← Nat.card_congr
    (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := permActD ceqHyp))).toEquiv]
  change Nat.card (Ceq ⧸ ΩIn Ceq) = 2 ^ 10
  exact natCard_Ceq_quot

instance Aeq_normal :
    Aeq.Normal := by
  rw [Aeq_eq_ker]
  infer_instance

@[expose] def thetaC :
    Ctwo →* Ppair := projP.comp piC

@[expose] def R2C :
    Subgroup Ctwo := Aeq.comap piC

@[expose] def R2 :
    Subgroup Dfull := R2C.map Ctwo.subtype

theorem R2C_eq_ker :
    R2C = thetaC.ker := by
  rw [R2C, Aeq_eq_ker, thetaC, MonoidHom.comap_ker]

theorem R2_le_Ctwo :
    R2 ≤ Ctwo := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem mem_R2_iff
    {g : Dfull} (hg : g ∈ Ctwo) : g ∈ R2 ↔ thetaC ⟨g, hg⟩ = 1 := by
  rw [← MonoidHom.mem_ker, ← R2C_eq_ker]
  constructor
  · rintro ⟨g', hg', e⟩
    have : g' = ⟨g, hg⟩ := Subtype.ext e
    rw [← this]
    exact hg'
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem sym3Hom_apply_zero_of_mem_Ptwo
    (g : Ntwo) (hg : (g : Dfull) ∈ Ptwo) : sym3Hom g 0 = 0 := by
  rw [sym3Hom_apply, vsharpEquiv_symm_zero, (smul_vX_eq_iff g).2 hg, vsharpEquiv_vX]

theorem perm_three_fix_zero : ∀ σ : Equiv.Perm (Fin 3), σ 0 = 0 → σ = 1 ∨ σ = Equiv.swap 1 2 := by
  decide

theorem sym3Hom_of_mem_Ptwo (g : Ntwo) (hg : (g : Dfull) ∈ Ptwo) :
    sym3Hom g = 1 ∨ sym3Hom g = Equiv.swap 1 2 :=
  perm_three_fix_zero _ (sym3Hom_apply_zero_of_mem_Ptwo g hg)

theorem sym3Hom_eq_swap {e : Ntwo} (hx : e • vX = vX) (hy : e • vY = vZ) (hz : e • vZ = vY) :
    sym3Hom e = Equiv.swap 1 2 := by
  have h0 : sym3Hom e 0 = 0 := by
    rw [sym3Hom_apply, vsharpEquiv_symm_zero, hx, vsharpEquiv_vX]
  have h1 : sym3Hom e 1 = 2 := by
    rw [sym3Hom_apply, vsharpEquiv_symm_one, hy, vsharpEquiv_vZ]
  have h2 : sym3Hom e 2 = 1 := by
    rw [sym3Hom_apply, vsharpEquiv_symm_two, hz, vsharpEquiv_vY]
  refine Equiv.ext fun k => ?_
  fin_cases k
  · exact h0.trans (by decide)
  · exact h1.trans (by decide)
  · exact h2.trans (by decide)

theorem mem_Ctwo_iff_sym3Hom (g : Ntwo) : (g : Dfull) ∈ Ctwo ↔ sym3Hom g = 1 := by
  rw [← MonoidHom.mem_ker, ker_sym3Hom, Subgroup.mem_subgroupOf]

theorem exists_Ehat_swap :
    ∃ e : Ntwo, (e : Dfull) ∈ Ehat ∧ (e : Dfull) ∈ Ptwo ∧ sym3Hom e = Equiv.swap 1 2 := by
  obtain ⟨e₀, he₀, he⟩ := exists_Ebar_swap
  have hJ : e₀ ∈ Jbar := Ebar_le_Jbar he₀
  have hP : iotaD e₀ ∈ Ptwo := by
    rw [mem_Ptwo_iff hJ]
    have h1 : jbarToKv ⟨e₀, hJ⟩ = 1 := by
      rw [← MonoidHom.mem_ker, ker_jbarToKv, Subgroup.mem_subgroupOf]
      exact he₀
    rw [h1]
    exact (monoSub ceqHyp).one_mem
  have hx : e₀ * xbar * e₀⁻¹ = xbar := by
    have := conj_xbar_of_mem_Jbar (Jbar.inv_mem hJ)
    rwa [inv_inv] at this
  refine ⟨⟨iotaD e₀, Ptwo_le_Ntwo hP⟩, ⟨e₀, he₀, rfl⟩, hP, sym3Hom_eq_swap ?_ ?_ ?_⟩
  · apply Subtype.ext
    change iotaD e₀ * xhat * (iotaD e₀)⁻¹ = xhat
    rw [← iotaD_xbar, ← map_inv, ← map_mul, ← map_mul, hx]
  · apply Subtype.ext
    change iotaD e₀ * iotaD ybar * (iotaD e₀)⁻¹ = yhat
    rw [yhat, ← map_inv, ← map_mul, ← map_mul, ← xbar_mul_zbar,
      show e₀ * (xbar * zbar) * e₀⁻¹ = (e₀ * xbar * e₀⁻¹) * (e₀ * zbar * e₀⁻¹) by group, hx, he,
      ← xbar_mul_zbar, ← mul_assoc, xbar_mul_self, one_mul]
  · apply Subtype.ext
    change iotaD e₀ * yhat * (iotaD e₀)⁻¹ = iotaD ybar
    rw [yhat, ← map_inv, ← map_mul, ← map_mul, he]

theorem jhatToKv_eq_one_of_mem_Ehat {g : Dfull} (hg : g ∈ Ehat) (hJ : g ∈ Jhat) :
    jhatToKv ⟨g, hJ⟩ = 1 := by
  rw [← MonoidHom.mem_ker, ker_jhatToKv, Subgroup.mem_subgroupOf]
  exact hg

theorem Kstab_mem_of_monoSub
    {k : OLq} (hk : k ∈ monoSub ceqHyp) :
    k ∈ Kstab (phi0 (coordOf rStar)) :=
  monoSub_le_Kstab_rStar hk

theorem piC_surjective :
    Function.Surjective piC := by
  intro m
  have hm : (((m : Kstab v0) : OLq)) ∈ monoSub ceqHyp := (mem_Mfr_iff _).1 m.2
  obtain ⟨j, hj⟩ := jhatToKv_surjective ⟨((m : Kstab v0) : OLq), Kstab_mem_of_monoSub hm⟩
  have hjP : (j : Dfull) ∈ Ptwo := by
    have h : j ∈ Ptwo.subgroupOf Jhat := by
      rw [Ptwo_eq_comap, Subgroup.mem_comap, Subgroup.mem_subgroupOf, hj]
      exact hm
    exact h
  have key : ∀ g : Dfull, ∀ hg : g ∈ Ctwo,
      ((jhatToKv ⟨g, Ctwo_le_Jhat hg⟩ : Kstab (phi0 (coordOf rStar))) : OLq) =
        ((m : Kstab v0) : OLq) → ∃ c, piC c = m := fun g hg h =>
    ⟨⟨g, hg⟩, Subtype.ext (Subtype.ext ((coe_piC _).trans h))⟩
  rcases sym3Hom_of_mem_Ptwo ⟨j, Ptwo_le_Ntwo hjP⟩ hjP with h1 | h1
  · have hC : (j : Dfull) ∈ Ctwo := (mem_Ctwo_iff_sym3Hom _).2 h1
    exact key _ hC (by rw [show (⟨(j : Dfull), Ctwo_le_Jhat hC⟩ : Jhat) = j from rfl, hj])
  · obtain ⟨e, heE, heP, hes⟩ := exists_Ehat_swap
    have hC : (j : Dfull) * (e : Dfull)⁻¹ ∈ Ctwo := by
      have : sym3Hom (⟨j, Ptwo_le_Ntwo hjP⟩ * e⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, hes, mul_inv_cancel]
      exact (mem_Ctwo_iff_sym3Hom _).2 this
    refine key _ hC ?_
    have e1 : (⟨(j : Dfull) * (e : Dfull)⁻¹, Ctwo_le_Jhat hC⟩ : Jhat) =
        j * (⟨e, Ptwo_le_Jhat heP⟩ : Jhat)⁻¹ := rfl
    rw [e1, map_mul, map_inv, jhatToKv_eq_one_of_mem_Ehat heE, inv_one, mul_one, hj]

theorem thetaC_surjective :
    Function.Surjective thetaC :=
  projP_surjective.comp piC_surjective

theorem natCard_ker_piC :
    Nat.card piC.ker = 2 ^ 22 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup piC.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ piC_surjective).toEquiv,
    natCard_Ctwo, natCard_Mfr] at h
  have h' : Nat.card piC.ker = 4194304 := by omega
  rw [h']
  norm_num

theorem natCard_R2C :
    Nat.card R2C = 2 ^ 32 := by
  rw [R2C, natCard_comap_of_surjective piC_surjective, natCard_ker_piC, natCard_Aeq]
  norm_num

theorem natCard_R2 :
    Nat.card R2 = 2 ^ 32 := by
  rw [R2, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), natCard_R2C]

theorem isPGroup_R2C :
    IsPGroup 2 R2C := IsPGroup.of_card natCard_R2C

theorem isPGroup_ker_thetaC :
    IsPGroup 2 thetaC.ker := R2C_eq_ker ▸ isPGroup_R2C

theorem mul_self_of_mem_Vhat {v : Dfull} (hv : v ∈ Vhat) : v * v = 1 := by
  obtain ⟨c, hc, rfl⟩ := hv
  rw [← map_mul, mul_self_of_mem_Vbar hc, map_one]

theorem Vhat_comm {v w : Dfull} (hv : v ∈ Vhat) (hw : w ∈ Vhat) : v * w = w * v := by
  have h1 : v⁻¹ = v := inv_eq_of_mul_eq_one_right (mul_self_of_mem_Vhat hv)
  have h2 : w⁻¹ = w := inv_eq_of_mul_eq_one_right (mul_self_of_mem_Vhat hw)
  have h3 : (v * w)⁻¹ = v * w :=
    inv_eq_of_mul_eq_one_right (mul_self_of_mem_Vhat (Vhat.mul_mem hv hw))
  rw [← h3, mul_inv_rev, h1, h2]

theorem Vhat_le_Ctwo : Vhat ≤ Ctwo := fun _ hv =>
  Subgroup.mem_centralizer_iff.2 fun _ hw => Vhat_comm hw hv

theorem Vhat_le_R2 :
    Vhat ≤ R2 := by
  intro v hv
  have hC := Vhat_le_Ctwo hv
  rw [mem_R2_iff hC, thetaC, MonoidHom.comp_apply]
  have h : piC ⟨v, hC⟩ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_piC, jhatToKv_eq_one_of_mem_Ehat (Vhat_le_Ehat hv)]
    rfl
  rw [h, map_one]

theorem fixesPair01_of_mem {q : AutPerm} (hq : q ∈ Ppair) : FixesPair01 q := (mem_Ppair_iff q).1 hq

@[expose] def gbar (q : Ppair) : Cbar :=
  kappa ⟨gLift q, gLift_mem_Cgen (fixesPair01_of_mem q.2)⟩

@[expose] def ghat (q : Ppair) : Dfull := iotaD (gbar q)

@[expose] def hbar : Cbar := kappa ⟨hE0, hE0_mem_Cgen⟩

@[expose] def hhat : Dfull := iotaD hbar

theorem commute_of_kappa {g g' : Cgen} (h : (g : SpaceB ≃ₗ[ℚ] SpaceB) * g' = g' * g) :
    kappa g * kappa g' = kappa g' * kappa g := by
  have e : g * g' = g' * g := Subtype.ext h
  rw [← map_mul, ← map_mul, e]

theorem gLift_mul_xmat (q : AutPerm) : gLift q * Generated.xmat = Generated.xmat * gLift q := by
  refine commute_of_conj_eq ?_
  change gLift q * rhoEquiv zQ * (gLift q)⁻¹ = rhoEquiv zQ
  rw [gLift_conj_rhoEquiv, conjQ_zQ]

theorem gbar_mul_xbar (q : Ppair) : gbar q * xbar = xbar * gbar q :=
  commute_of_kappa (g := ⟨gLift q, gLift_mem_Cgen (fixesPair01_of_mem q.2)⟩) (g' := xC)
    (gLift_mul_xmat q)

theorem gbar_mul_taubar (q : Ppair) : gbar q * taubar = taubar * gbar q :=
  kappa_gLift_mul_taubar _

theorem gbar_mul_hbar (q : Ppair) : gbar q * hbar = hbar * gbar q :=
  kappa_gLift_mul_kappa_hE0 (fixesPair01_of_mem q.2) _

theorem commute_conj {G : Type*} [Group G] {g t a : G} (ht : g * t = t * g) (ha : g * a = a * g) :
    g * (t * a * t⁻¹) = (t * a * t⁻¹) * g := by
  have ht' : g * t⁻¹ = t⁻¹ * g := by
    calc g * t⁻¹ = t⁻¹ * (t * g) * t⁻¹ := by group
      _ = t⁻¹ * (g * t) * t⁻¹ := by rw [ht]
      _ = t⁻¹ * g := by group
  calc g * (t * a * t⁻¹) = t * (g * a) * t⁻¹ := by
        rw [← mul_assoc, ← mul_assoc, ht, mul_assoc t g a]
    _ = t * a * (g * t⁻¹) := by rw [ha]; group
    _ = (t * a * t⁻¹) * g := by rw [ht']; group

theorem gbar_mul_mem_Vbar (q : Ppair) {c : Cbar} (hc : c ∈ Vbar) : gbar q * c = c * gbar q := by
  rcases (mem_Vbar_iff c).1 hc with rfl | rfl | rfl | rfl
  · rw [mul_one, one_mul]
  · exact gbar_mul_xbar q
  · rw [← taubar_conj_xbar]
    exact commute_conj (gbar_mul_taubar q) (gbar_mul_xbar q)
  · rw [← taubar_conj_ybar, ← taubar_conj_xbar]
    exact commute_conj (gbar_mul_taubar q) (commute_conj (gbar_mul_taubar q) (gbar_mul_xbar q))

theorem ghat_mem_Ctwo (q : Ppair) : ghat q ∈ Ctwo := by
  refine Subgroup.mem_centralizer_iff.2 ?_
  rintro _ ⟨c, hc, rfl⟩
  rw [ghat, ← map_mul, ← map_mul, gbar_mul_mem_Vbar q hc]

theorem ghat_mul_tauhat (q : Ppair) : ghat q * tauhat = tauhat * ghat q := by
  rw [ghat, tauhat, ← map_mul, ← map_mul, gbar_mul_taubar]

theorem ghat_mul_hhat (q : Ppair) : ghat q * hhat = hhat * ghat q := by
  rw [ghat, hhat, ← map_mul, ← map_mul, gbar_mul_hbar]

@[expose] def ghatC (q : Ppair) : Ctwo := ⟨ghat q, ghat_mem_Ctwo q⟩

theorem gPair_snd (q : AutPerm) : (gPair q).1.2 = PO q := by
  rw [gPair, Subgroup.coe_mul, Prod.snd_mul, coe_rhoPair, mul_one]
  rfl

theorem gbar_mem_Jbar (q : Ppair) : gbar q ∈ Jbar :=
  kappa_mem_Jbar (gLift_mem_Jstar (fixesPair01_of_mem q.2))

theorem jhatToKv_ghat (q : Ppair) :
    ((jhatToKv ⟨ghat q, Ctwo_le_Jhat (ghat_mem_Ctwo q)⟩ : Kstab (phi0 (coordOf rStar))) : OLq) =
      (QuotientGroup.mk (PO (q : AutPerm)))⁻¹ := by
  have e : (⟨ghat q, Ctwo_le_Jhat (ghat_mem_Ctwo q)⟩ : Jhat) =
      jhatEquiv ⟨gbar q, gbar_mem_Jbar q⟩ := Subtype.ext rfl
  rw [e, jhatToKv_jhatEquiv]
  have h := coe_jbarToKv_kappa (g₀ := ⟨gLift q, gLift_mem_Cgen (fixesPair01_of_mem q.2)⟩)
    (gLift_mem_Jstar (fixesPair01_of_mem q.2)) (p := gPair q) (gLift_eq q).symm
  rw [gPair_snd] at h
  exact h

theorem piC_ghatC
    (q : Ppair) : piC (ghatC q) = MfrEquiv ⟨1, q⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_piC, coe_MfrEquiv]
  change _ = monoD ceqHyp ⟨Multiplicative.ofAdd (Submodule.Quotient.mk 0), q⟩
  rw [monoD_mk, map_zero, gO_zero, one_mul, PO_inv, QuotientGroup.mk_inv]
  exact jhatToKv_ghat q

theorem thetaC_ghatC
    (q : Ppair) : thetaC (ghatC q) = q := by
  rw [thetaC, MonoidHom.comp_apply, piC_ghatC, projP_MfrEquiv]

theorem hE0_mul_xmat : hE0 * Generated.xmat = Generated.xmat * hE0 := by
  change rhoEquiv (DQ e0Cls) * rhoEquiv zQ = rhoEquiv zQ * rhoEquiv (DQ e0Cls)
  rw [← rhoEquiv_mul, ← rhoEquiv_mul, Subgroup.mem_center_iff.1 Short.zQ_mem_center (DQ e0Cls)]

theorem hE0_mul_hE0 : hE0 * hE0 = 1 := Generated.OddCocode.hCocode_mul_self e0Cls

theorem hE0_mul_tauB_mul_hE0 : hE0 * tauB * hE0 = tauB⁻¹ :=
  Generated.OddCocode.hCocode_mul_tauB_mul pair_ΩC_mk_single

theorem hbar_mul_self : hbar * hbar = 1 := by
  rw [hbar, ← map_mul]
  have : (⟨hE0, hE0_mem_Cgen⟩ : Cgen) * ⟨hE0, hE0_mem_Cgen⟩ = 1 := Subtype.ext hE0_mul_hE0
  rw [this, map_one]

theorem hbar_inv : hbar⁻¹ = hbar := inv_eq_of_mul_eq_one_right hbar_mul_self

theorem hbar_mul_xbar : hbar * xbar = xbar * hbar :=
  commute_of_kappa (g := ⟨hE0, hE0_mem_Cgen⟩) (g' := xC) hE0_mul_xmat

theorem hbar_conj_xbar : hbar * xbar * hbar⁻¹ = xbar := by
  rw [hbar_mul_xbar, mul_inv_cancel_right]

theorem hbar_conj_taubar : hbar * taubar * hbar⁻¹ = taubar⁻¹ := by
  rw [hbar_inv, hbar, taubar, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  exact Subtype.ext hE0_mul_tauB_mul_hE0

theorem conj_conj_inv {G : Type*} [Group G] (h t a : G) :
    h * (t * a * t⁻¹) * h⁻¹ = (h * t * h⁻¹) * (h * a * h⁻¹) * (h * t * h⁻¹)⁻¹ := by group

theorem hbar_conj_ybar : hbar * ybar * hbar⁻¹ = zbar := by
  rw [← taubar_conj_xbar, conj_conj_inv, hbar_conj_taubar, hbar_conj_xbar, inv_inv]
  exact taubar_inv_conj_xbar

theorem zbar_eq_xbar_mul_ybar : zbar = xbar * ybar := by
  rw [← xbar_mul_zbar, ← mul_assoc, xbar_mul_self, one_mul]

theorem hbar_conj_zbar : hbar * zbar * hbar⁻¹ = ybar := by
  rw [zbar_eq_xbar_mul_ybar, show hbar * (xbar * ybar) * hbar⁻¹ =
    (hbar * xbar * hbar⁻¹) * (hbar * ybar * hbar⁻¹) by group, hbar_conj_xbar, hbar_conj_ybar,
    xbar_mul_zbar]

theorem hbar_conj_mem_Vbar {c : Cbar} (hc : c ∈ Vbar) : hbar * c * hbar⁻¹ ∈ Vbar := by
  rcases (mem_Vbar_iff c).1 hc with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact Vbar.one_mem
  · rw [hbar_conj_xbar]
    exact xbar_mem_Vbar
  · rw [hbar_conj_ybar]
    exact zbar_mem_Vbar
  · rw [hbar_conj_zbar]
    exact ybar_mem_Vbar

theorem hhat_mem_Ntwo : hhat ∈ Ntwo := by
  change hhat ∈ Subgroup.normalizer (Vhat : Set Dfull)
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨c, hc, rfl⟩ := hn
  rw [hhat, ← map_inv, ← map_mul, ← map_mul]
  exact ⟨_, hbar_conj_mem_Vbar hc, rfl⟩

@[expose] def hhatN : Ntwo := ⟨hhat, hhat_mem_Ntwo⟩

theorem sym3Hom_hhatN : sym3Hom hhatN = Equiv.swap 1 2 := by
  refine sym3Hom_eq_swap ?_ ?_ ?_
  · apply Subtype.ext
    change hhat * xhat * hhat⁻¹ = xhat
    rw [hhat, ← iotaD_xbar, ← map_inv, ← map_mul, ← map_mul, hbar_conj_xbar]
  · apply Subtype.ext
    change hhat * iotaD ybar * hhat⁻¹ = yhat
    rw [hhat, yhat, ← map_inv, ← map_mul, ← map_mul, hbar_conj_ybar]
  · apply Subtype.ext
    change hhat * yhat * hhat⁻¹ = iotaD ybar
    rw [hhat, yhat, ← map_inv, ← map_mul, ← map_mul, hbar_conj_zbar]

end CFSG.Monster.B.TwoA
