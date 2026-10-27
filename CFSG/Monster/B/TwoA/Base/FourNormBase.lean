module

public import CFSG.Monster.B.TwoA.Base.FullCent
public import CFSG.Monster.B.TwoA.Base.FrameBase
public import CFSG.Monster.B.TwoA.Base.GroupAux

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

open scoped commutatorElement

theorem phi0_coordOf_wQ : phi0 (coordOf wQ) = twoΩCls := by
  rw [← toAdd_phi_mk wQ, phi_wQ, Griess.classOf_eq_cls two_omega_mem]
  rfl

theorem wQ_mem_centralizer :
    wQ ∈ Subgroup.centralizer {rStar} := by
  rw [mem_centralizer_iff_bL, phi0_coordOf_rStar, phi0_coordOf_wQ]
  exact bL_v0_twoΩCls

theorem zC_eq :
    zC = ⟨rhoEquiv wQ, rhoEquiv_mem_Cgen wQ_mem_centralizer⟩ :=
  Subtype.ext (xmatTau2_eq.trans rhoEquiv_wQ.symm)

theorem zbar_eq :

    zbar = kappa ⟨rhoEquiv wQ, rhoEquiv_mem_Cgen wQ_mem_centralizer⟩ := by
  show kappa zC = _
  rw [zC_eq]

theorem zbar_mem_Ebar :
    zbar ∈ Ebar := by
  rw [zbar_eq]
  exact kappa_rho_mem_Ebar wQ_mem_centralizer

theorem twoΩCls_mem_vPerp_rStar :
    twoΩCls ∈ vPerpL (phi0 (coordOf rStar)) := by
  rw [phi0_coordOf_rStar]
  exact twoΩCls_mem_vPerpL

theorem psiBar_zbar :
    psiBar ⟨zbar, zbar_mem_Ebar⟩ =
    Multiplicative.ofAdd (Submodule.Quotient.mk ⟨twoΩCls, twoΩCls_mem_vPerp_rStar⟩) := by
  have e : (⟨zbar, zbar_mem_Ebar⟩ : Ebar) =
      ⟨kappa ⟨rhoEquiv wQ, rhoEquiv_mem_Cgen wQ_mem_centralizer⟩,
        kappa_rho_mem_Ebar wQ_mem_centralizer⟩ := Subtype.ext zbar_eq
  rw [e, psiBar_kappa_rho wQ_mem_centralizer]
  congr 2
  exact Subtype.ext phi0_coordOf_wQ

theorem psiBar_xbar : psiBar ⟨xbar, xbar_mem_Ebar⟩ = 1 :=
  (psiBar_eq_one_iff _).2 (.inr rfl)

theorem xbar_mul_zbar : xbar * zbar = ybar := by
  have hmem : xbar * zbar ∈ Vbar := Vbar.mul_mem xbar_mem_Vbar zbar_mem_Vbar
  rcases (mem_Vbar_iff _).1 hmem with h | h | h | h
  · exfalso
    have : zbar = xbar := by
      have := congrArg (xbar * ·) h
      simp only [mul_one, ← mul_assoc, xbar_mul_self, one_mul] at this
      exact this
    exact zbar_ne_xbar this
  · exfalso
    have : zbar = 1 := by
      have := congrArg (xbar⁻¹ * ·) h
      simpa using this
    exact zbar_ne_one this
  · exact h
  · exfalso
    have : xbar = 1 := by
      have := congrArg (· * zbar⁻¹) h
      simpa using this
    exact xbar_ne_one this

theorem ybar_mem_Ebar :
    ybar ∈ Ebar := by
  rw [← xbar_mul_zbar]
  exact Ebar.mul_mem xbar_mem_Ebar zbar_mem_Ebar

theorem Vbar_le_Ebar :
    Vbar ≤ Ebar := by
  intro c hc
  rcases (mem_Vbar_iff c).1 hc with rfl | rfl | rfl | rfl
  · exact Ebar.one_mem
  · exact xbar_mem_Ebar
  · exact ybar_mem_Ebar
  · exact zbar_mem_Ebar

theorem Kstab_rStar_eq : Kstab (phi0 (coordOf rStar)) = Kstab v0 :=
  congrArg Kstab phi0_coordOf_rStar

theorem mem_Kstab_v0_of {k : OLq} (hk : k ∈ Kstab (phi0 (coordOf rStar))) : k ∈ Kstab v0 :=
  Kstab_rStar_eq ▸ hk

theorem wAct_fix_iff
    (k : Kstab (phi0 (coordOf rStar))) :
    wAct _ k (Submodule.Quotient.mk ⟨twoΩCls, twoΩCls_mem_vPerp_rStar⟩) =
        Submodule.Quotient.mk ⟨twoΩCls, twoΩCls_mem_vPerp_rStar⟩ ↔
      (k : OLq) ∈ monoSub ceqHyp := by
  rw [wAct_mk, Submodule.Quotient.eq, mem_monoSub_ceq_iff (mem_Kstab_v0_of k.2),
    ← kOp_sub_mem_vLineL_iff (mem_Kstab_v0_of k.2)]
  have key : ∀ x : L2, x ∈ vLineL (phi0 (coordOf rStar)) ↔ x ∈ vLineL v0 := fun x => by
    rw [phi0_coordOf_rStar]
  exact key _

theorem conj_xbar_of_mem_Jbar
    {g : Cbar} (hg : g ∈ Jbar) : g⁻¹ * xbar * g = xbar := by
  rw [← centralizer_xbar] at hg
  have h := Subgroup.mem_centralizer_singleton_iff.1 hg
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem conj_zbar_mem_Vbar_iff
    {g : Cbar} (hg : g ∈ Jbar) :
    g⁻¹ * zbar * g ∈ Vbar ↔ (jbarToKv ⟨g, hg⟩ : OLq) ∈ monoSub ceqHyp := by
  rw [← wAct_fix_iff]
  have hc := psiBar_conj hg zbar_mem_Ebar
  rw [psiBar_zbar] at hc
  constructor
  · intro hV
    have hψ : psiBar ⟨g⁻¹ * zbar * g, conj_mem_Ebar hg zbar_mem_Ebar⟩ =
        psiBar ⟨zbar, zbar_mem_Ebar⟩ := by
      rcases (mem_Vbar_iff _).1 hV with h | h | h | h
      · exfalso
        have : zbar = 1 := by
          have := congrArg (g * · * g⁻¹) h
          simpa [mul_assoc] using this
        exact zbar_ne_one this
      · exfalso
        have : zbar = xbar := by
          have h2 := conj_xbar_of_mem_Jbar hg
          have := congrArg (g * · * g⁻¹) (h.trans h2.symm)
          simpa [mul_assoc] using this
        exact zbar_ne_xbar this
      · have e : (⟨g⁻¹ * zbar * g, conj_mem_Ebar hg zbar_mem_Ebar⟩ : Ebar) =
            ⟨xbar, xbar_mem_Ebar⟩ * ⟨zbar, zbar_mem_Ebar⟩ :=
          Subtype.ext (h.trans xbar_mul_zbar.symm)
        rw [e, map_mul, psiBar_xbar, one_mul]
      · exact congrArg psiBar (Subtype.ext h)
    rw [hc, psiBar_zbar] at hψ
    exact Multiplicative.ofAdd.injective hψ
  · intro hw
    simp only [toAdd_ofAdd] at hc
    rw [hw, ← psiBar_zbar] at hc
    have h1 : psiBar (⟨zbar, zbar_mem_Ebar⟩⁻¹ *
        ⟨g⁻¹ * zbar * g, conj_mem_Ebar hg zbar_mem_Ebar⟩) = 1 := by
      rw [map_mul, map_inv, hc, inv_mul_cancel]
    rcases (psiBar_eq_one_iff _).1 h1 with h | h
    · have := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at this
      rw [inv_mul_eq_one.1 this |>.symm]
      exact zbar_mem_Vbar
    · have := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [show g⁻¹ * zbar * g = zbar * xbar by rw [← this, mul_inv_cancel_left]]
      exact Vbar.mul_mem zbar_mem_Vbar xbar_mem_Vbar

theorem zbar_not_mem_center :
    (⟨zbar, zbar_mem_Ebar⟩ : Ebar) ∉ Subgroup.center Ebar := by
  rw [center_Ebar, Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbarE]
  rintro (h | h)
  · exact zbar_ne_one (congrArg Subtype.val h)
  · exact zbar_ne_xbar (congrArg Subtype.val h)

theorem exists_Ebar_swap :
    ∃ e ∈ Ebar, e * zbar * e⁻¹ = ybar := by
  have hE := Ebar_extraspecial.1
  obtain ⟨e, he⟩ : ∃ e : Ebar, e * ⟨zbar, zbar_mem_Ebar⟩ ≠ ⟨zbar, zbar_mem_Ebar⟩ * e := by
    by_contra h
    push Not at h
    exact zbar_not_mem_center (Subgroup.mem_center_iff.2 fun e => (h e))
  have hc : ⁅e, (⟨zbar, zbar_mem_Ebar⟩ : Ebar)⁆ ∈ Subgroup.center Ebar := by
    rw [← hE.2.1]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top e) (Subgroup.mem_top _)
  rw [center_Ebar, Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbarE] at hc
  rcases hc with h | h
  · exfalso
    apply he
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  · refine ⟨e, e.2, ?_⟩
    have h' := congrArg Subtype.val h
    rw [commutatorElement_def] at h'
    change (e : Cbar) * zbar * (e : Cbar)⁻¹ * zbar⁻¹ = xbar at h'
    rw [← xbar_mul_zbar, ← h', inv_mul_cancel_right]

@[expose] noncomputable def Vhat : Subgroup Dfull := Vbar.map iotaD

@[expose] noncomputable def yhat : Dfull := iotaD zbar

theorem tauhat_sq_conj_xhat : tauhat ^ 2 * xhat * (tauhat ^ 2)⁻¹ = yhat := by
  rw [tauhat, ← iotaD_xbar, yhat, ← map_pow, ← map_inv, ← map_mul, ← map_mul,
    ← conj_conj_eq_sq, taubar_conj_xbar, taubar_conj_ybar]

theorem xhat_mul_yhat : xhat * yhat = iotaD ybar := by
  rw [← iotaD_xbar, yhat, ← map_mul, xbar_mul_zbar]

theorem mem_Vhat_iff (d : Dfull) :
    d ∈ Vhat ↔ d = 1 ∨ d = xhat ∨ d = xhat * yhat ∨ d = yhat := by
  rw [xhat_mul_yhat]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases (mem_Vbar_iff c).1 hc with rfl | rfl | rfl | rfl
    · exact .inl (map_one _)
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Vhat.one_mem
    · exact ⟨xbar, xbar_mem_Vbar, rfl⟩
    · exact ⟨ybar, ybar_mem_Vbar, rfl⟩
    · exact ⟨zbar, zbar_mem_Vbar, rfl⟩

theorem Vhat_le_Ehat :
    Vhat ≤ Ehat := Subgroup.map_mono Vbar_le_Ebar

theorem isKleinFour_Vhat : IsKleinFour Vhat :=
  ⟨by rw [Vhat, ← Nat.card_congr (Vbar.equivMapOfInjective iotaD iotaD_injective).toEquiv]
      exact isKleinFour_Vbar.card_four,
    by rw [Vhat, ← Monoid.exponent_eq_of_mulEquiv (Vbar.equivMapOfInjective iotaD iotaD_injective)]
       exact isKleinFour_Vbar.exponent_two⟩

theorem xhat_mem_Vhat : xhat ∈ Vhat := (mem_Vhat_iff _).2 (.inr (.inl rfl))

theorem yhat_mem_Vhat : yhat ∈ Vhat := (mem_Vhat_iff _).2 (.inr (.inr (.inr rfl)))

@[expose] noncomputable def Ptwo : Subgroup Dfull := Jhat ⊓ Subgroup.normalizer (Vhat : Set Dfull)

@[expose] noncomputable def Ntwo : Subgroup Dfull := Subgroup.normalizer (Vhat : Set Dfull)

@[expose] noncomputable def Ctwo : Subgroup Dfull := Subgroup.centralizer (Vhat : Set Dfull)

theorem iotaD_mem_normalizer_iff {g : Cbar} (hg : g ∈ Jbar) :
    iotaD g ∈ Ntwo ↔ g⁻¹ * zbar * g ∈ Vbar := by
  constructor
  · intro h
    have h1 := (Subgroup.mem_normalizer_iff''.1 h yhat).1 yhat_mem_Vhat
    rw [yhat, ← map_inv, ← map_mul, ← map_mul] at h1
    exact (Subgroup.mem_map_iff_mem iotaD_injective).1 h1
  · intro h
    change iotaD g ∈ Subgroup.normalizer (Vhat : Set Dfull)
    rw [← Subgroup.inv_mem_iff]
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨c, hc, rfl⟩ := hn
    rw [inv_inv, ← map_inv, ← map_mul, ← map_mul]
    refine ⟨g⁻¹ * c * g, ?_, rfl⟩
    rcases (mem_Vbar_iff c).1 hc with rfl | rfl | rfl | rfl
    · rw [mul_one, inv_mul_cancel]
      exact Vbar.one_mem
    · rw [conj_xbar_of_mem_Jbar hg]
      exact xbar_mem_Vbar
    · rw [← xbar_mul_zbar, show g⁻¹ * (xbar * zbar) * g = (g⁻¹ * xbar * g) * (g⁻¹ * zbar * g) by
        group, conj_xbar_of_mem_Jbar hg]
      exact Vbar.mul_mem xbar_mem_Vbar h
    · exact h

theorem mem_Ptwo_iff
    {g : Cbar} (hg : g ∈ Jbar) :
    iotaD g ∈ Ptwo ↔ (jbarToKv ⟨g, hg⟩ : OLq) ∈ monoSub ceqHyp := by
  have hJ : iotaD g ∈ Jhat := by rw [Jhat_eq_map]; exact ⟨g, hg, rfl⟩
  rw [Ptwo, Subgroup.mem_inf, ← conj_zbar_mem_Vbar_iff hg, ← iotaD_mem_normalizer_iff hg]
  exact ⟨fun h => h.2, fun h => ⟨hJ, h⟩⟩

@[expose] noncomputable def jhatEquiv : Jbar ≃* Jhat :=
  (Jbar.equivMapOfInjective iotaD iotaD_injective).trans (MulEquiv.subgroupCongr Jhat_eq_map.symm)

theorem coe_jhatEquiv (g : Jbar) : (jhatEquiv g : Dfull) = iotaD g := rfl

@[expose] noncomputable def jhatToKv : Jhat →* Kstab (phi0 (coordOf rStar)) :=
  jbarToKv.comp jhatEquiv.symm.toMonoidHom

theorem jhatToKv_jhatEquiv (g : Jbar) : jhatToKv (jhatEquiv g) = jbarToKv g := by
  change jbarToKv (jhatEquiv.symm (jhatEquiv g)) = jbarToKv g
  rw [MulEquiv.symm_apply_apply]

theorem jhatToKv_surjective :
    Function.Surjective jhatToKv :=
  jbarToKv_surjective.comp jhatEquiv.symm.surjective

theorem ker_jhatToKv : jhatToKv.ker = Ehat.subgroupOf Jhat := by
  ext d
  obtain ⟨g, rfl⟩ := jhatEquiv.surjective d
  rw [MonoidHom.mem_ker, jhatToKv_jhatEquiv, ← MonoidHom.mem_ker, ker_jbarToKv,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_jhatEquiv, Ehat]
  exact (Subgroup.mem_map_iff_mem iotaD_injective).symm

theorem Ptwo_eq_comap :
    Ptwo.subgroupOf Jhat =
    ((monoSub ceqHyp).subgroupOf (Kstab (phi0 (coordOf rStar)))).comap jhatToKv := by
  ext d
  obtain ⟨g, rfl⟩ := jhatEquiv.surjective d
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf, jhatToKv_jhatEquiv,
    coe_jhatEquiv]
  exact mem_Ptwo_iff g.2

theorem monoSub_le_Kstab_rStar :
    monoSub ceqHyp ≤ Kstab (phi0 (coordOf rStar)) :=
  Kstab_rStar_eq ▸ monoSub_ceq_le_Kstab

theorem natCard_M_in :

    Nat.card ((monoSub ceqHyp).subgroupOf (Kstab (phi0 (coordOf rStar)))) =
    908328960 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe monoSub_le_Kstab_rStar).toEquiv,
    ← Nat.card_congr mfrEquivMono.toEquiv, natCard_Mfr]

theorem natCard_Ehat : Nat.card Ehat = 2 ^ 23 := by
  rw [Ehat, ← Nat.card_congr (Ebar.equivMapOfInjective iotaD iotaD_injective).toEquiv]
  exact Ebar_extraspecial.2

theorem natCard_ker_jhatToKv : Nat.card jhatToKv.ker = 2 ^ 23 := by
  rw [ker_jhatToKv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ehat_le_Jhat).toEquiv,
    natCard_Ehat]

theorem natCard_Ptwo :
    Nat.card Ptwo = 7619615580487680 := by
  have hle : Ptwo ≤ Jhat := inf_le_left
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Ptwo_eq_comap,
    natCard_comap_of_surjective jhatToKv_surjective, natCard_ker_jhatToKv, natCard_M_in]
  norm_num

@[expose] noncomputable def P2J : Subgroup Jhat :=
  ((monoSub ceqHyp).subgroupOf (Kstab (phi0 (coordOf rStar)))).comap jhatToKv

theorem Ptwo_subgroupOf_eq :
    Ptwo.subgroupOf Jhat = P2J := Ptwo_eq_comap

@[expose] noncomputable def ptwoQuotEquiv :
    P2J ⧸ (jhatToKv.ker.subgroupOf P2J) ≃* Mfr :=
  (QuotientGroup.quotientMulEquivOfEq (ker_comapRestrict jhatToKv _).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _
      (comapRestrict_surjective jhatToKv_surjective _)).trans
      ((Subgroup.subgroupOfEquivOfLe monoSub_le_Kstab_rStar).trans mfrEquivMono.symm))

theorem tauhat_mem_Ntwo : tauhat ∈ Ntwo := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨c, hc, rfl⟩ := hn
  rw [tauhat, ← map_inv, ← map_mul, ← map_mul]
  exact ⟨_, taubar_conj_mem_Vbar hc, rfl⟩

theorem Ptwo_le_Ntwo : Ptwo ≤ Ntwo := inf_le_right

theorem Ptwo_le_Jhat : Ptwo ≤ Jhat := inf_le_left

abbrev Vsharp : Type := {d : Dfull // d ∈ Vhat ∧ d ≠ 1}

theorem conj_mem_Vhat {g : Dfull} (hg : g ∈ Ntwo) {d : Dfull} (hd : d ∈ Vhat) :
    g * d * g⁻¹ ∈ Vhat :=
  (Subgroup.mem_normalizer_iff.1 hg d).1 hd

@[expose, instance_reducible] noncomputable def vAction : MulAction Ntwo Vsharp where
  smul g v := ⟨(g : Dfull) * v * (g : Dfull)⁻¹, conj_mem_Vhat g.2 v.2.1, fun h =>
    v.2.2 (by
      have := congrArg (fun d => (g : Dfull)⁻¹ * d * g) h
      simpa [mul_assoc] using this)⟩
  one_smul v := Subtype.ext (by
    change ((1 : Ntwo) : Dfull) * v * ((1 : Ntwo) : Dfull)⁻¹ = v
    simp)
  mul_smul g h v := Subtype.ext (by
    change ((g * h : Ntwo) : Dfull) * v * ((g * h : Ntwo) : Dfull)⁻¹ =
      (g : Dfull) * ((h : Dfull) * v * (h : Dfull)⁻¹) * (g : Dfull)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

attribute [local instance] vAction

theorem coe_smul_vsharp (g : Ntwo) (v : Vsharp) :
    ((g • v : Vsharp) : Dfull) = (g : Dfull) * v * (g : Dfull)⁻¹ := rfl

theorem xhat_ne_one : xhat ≠ 1 := by
  rw [← iotaD_xbar]
  exact fun h => xbar_ne_one (iotaD_injective (h.trans (map_one _).symm))

theorem iotaD_ybar_ne_one : iotaD ybar ≠ 1 :=
  fun h => ybar_ne_one (iotaD_injective (h.trans (map_one _).symm))

theorem yhat_ne_one : yhat ≠ 1 :=
  fun h => zbar_ne_one (iotaD_injective (h.trans (map_one _).symm))

@[expose] noncomputable def vX : Vsharp := ⟨xhat, xhat_mem_Vhat, xhat_ne_one⟩

@[expose] noncomputable def vY : Vsharp :=
  ⟨iotaD ybar, ⟨ybar, ybar_mem_Vbar, rfl⟩, iotaD_ybar_ne_one⟩

@[expose] noncomputable def vZ : Vsharp := ⟨yhat, yhat_mem_Vhat, yhat_ne_one⟩

theorem vsharp_cases (v : Vsharp) : v = vX ∨ v = vY ∨ v = vZ := by
  rcases (mem_Vhat_iff v.1).1 v.2.1 with h | h | h | h
  · exact absurd h v.2.2
  · exact .inl (Subtype.ext h)
  · exact .inr (.inl (Subtype.ext (h.trans xhat_mul_yhat)))
  · exact .inr (.inr (Subtype.ext h))

theorem vX_ne_vY : vX ≠ vY := fun h =>
  xbar_ne_ybar (iotaD_injective (congrArg Subtype.val h))

theorem vY_ne_vZ : vY ≠ vZ := fun h =>
  ybar_ne_zbar (iotaD_injective (congrArg Subtype.val h))

theorem vZ_ne_vX : vZ ≠ vX := fun h =>
  zbar_ne_xbar (iotaD_injective (congrArg Subtype.val h))

open _root_.Classical in
@[expose] noncomputable def vsharpEquiv : Vsharp ≃ Fin 3 where
  toFun v := if v = vX then 0 else if v = vY then 1 else 2
  invFun := ![vX, vY, vZ]
  left_inv v := by
    rcases vsharp_cases v with rfl | rfl | rfl
    · simp
    · simp [vX_ne_vY.symm]
    · simp [vZ_ne_vX, vY_ne_vZ.symm]
  right_inv k := by
    fin_cases k
    · simp
    · simp [vX_ne_vY.symm]
    · simp [vZ_ne_vX, vY_ne_vZ.symm]

theorem natCard_vsharp : Nat.card Vsharp = 3 := by
  rw [Nat.card_congr vsharpEquiv, Nat.card_fin]

@[expose] noncomputable def tauN : Ntwo := ⟨tauhat, tauhat_mem_Ntwo⟩

theorem tauN_vX : tauN • vX = vY := Subtype.ext tauhat_conj_xhat

theorem tauN_vY : tauN • vY = vZ := Subtype.ext (by
  change tauhat * iotaD ybar * tauhat⁻¹ = yhat
  rw [tauhat, yhat, ← map_inv, ← map_mul, ← map_mul, taubar_conj_ybar])

theorem tauN_vZ : tauN • vZ = vX := Subtype.ext (by
  change tauhat * yhat * tauhat⁻¹ = xhat
  rw [tauhat, yhat, ← iotaD_xbar, ← map_inv, ← map_mul, ← map_mul, taubar_conj_zbar])

theorem smul_vX_eq_iff
    (g : Ntwo) : g • vX = vX ↔ (g : Dfull) ∈ Ptwo := by
  rw [← Subtype.coe_inj, coe_smul_vsharp]
  change (g : Dfull) * xhat * (g : Dfull)⁻¹ = xhat ↔ _
  rw [Ptwo, Subgroup.mem_inf, ← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff,
    mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩

theorem stabilizer_vX :
    MulAction.stabilizer Ntwo vX = Ptwo.subgroupOf Ntwo := by
  ext g
  rw [MulAction.mem_stabilizer_iff, smul_vX_eq_iff, Subgroup.mem_subgroupOf]

theorem orbit_vX : MulAction.orbit Ntwo vX = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro v
  rcases vsharp_cases v with rfl | rfl | rfl
  · exact MulAction.mem_orbit_self _
  · exact ⟨tauN, tauN_vX⟩
  · exact ⟨tauN * tauN, by
      change (tauN * tauN) • vX = vZ
      rw [mul_smul, tauN_vX, tauN_vY]⟩

theorem index_Ptwo_Ntwo : (Ptwo.subgroupOf Ntwo).index = 3 := by
  rw [← stabilizer_vX, MulAction.index_stabilizer, orbit_vX, Set.ncard_univ, natCard_vsharp]

theorem Ntwo_eq_closure :
    Ntwo = Subgroup.closure (insert tauhat (Ptwo : Set Dfull)) := by
  apply le_antisymm
  · intro g hg
    have hmem : ∀ h : Ntwo, h • vX = vX → (h : Dfull) ∈
        Subgroup.closure (insert tauhat (Ptwo : Set Dfull)) := fun h hh =>
      Subgroup.subset_closure (Set.mem_insert_of_mem _ ((smul_vX_eq_iff h).1 hh))
    have htau : tauhat ∈ Subgroup.closure (insert tauhat (Ptwo : Set Dfull)) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    rcases vsharp_cases ((⟨g, hg⟩ : Ntwo) • vX) with h | h | h
    · exact hmem _ h
    · have h2 := hmem (tauN * tauN * ⟨g, hg⟩) (by rw [mul_smul, mul_smul, h, tauN_vY, tauN_vZ])
      have e : g = (tauhat * tauhat)⁻¹ * ((tauN * tauN * ⟨g, hg⟩ : Ntwo) : Dfull) := by
        change g = (tauhat * tauhat)⁻¹ * (tauhat * tauhat * g)
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ htau htau)) h2
    · have h2 := hmem (tauN * ⟨g, hg⟩) (by rw [mul_smul, h, tauN_vZ])
      have e : g = tauhat⁻¹ * ((tauN * ⟨g, hg⟩ : Ntwo) : Dfull) := by
        change g = tauhat⁻¹ * (tauhat * g)
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htau) h2
  · rw [Subgroup.closure_le]
    rintro _ (rfl | h)
    · exact tauhat_mem_Ntwo
    · exact Ptwo_le_Ntwo h

theorem Ntwo_le_Shat : Ntwo ≤ Shat := by
  rw [Ntwo_eq_closure, Subgroup.closure_le]
  rintro _ (rfl | h)
  · exact ⟨taubar, rfl⟩
  · exact Jhat_le_Shat (Ptwo_le_Jhat h)

@[expose] noncomputable def sym3Hom : Ntwo →* Equiv.Perm (Fin 3) :=
  (Equiv.permCongrHom vsharpEquiv).toMonoidHom.comp (MulAction.toPermHom Ntwo Vsharp)

theorem sym3Hom_apply (g : Ntwo) (k : Fin 3) :
    sym3Hom g k = vsharpEquiv (g • vsharpEquiv.symm k) := rfl

theorem vsharpEquiv_vX : vsharpEquiv vX = 0 := by simp [vsharpEquiv]

theorem vsharpEquiv_vY : vsharpEquiv vY = 1 := by simp [vsharpEquiv, vX_ne_vY.symm]

theorem vsharpEquiv_vZ : vsharpEquiv vZ = 2 := by
  simp [vsharpEquiv, vZ_ne_vX, vY_ne_vZ.symm]

theorem vsharpEquiv_symm_zero : vsharpEquiv.symm 0 = vX := rfl

theorem vsharpEquiv_symm_one : vsharpEquiv.symm 1 = vY := rfl

theorem vsharpEquiv_symm_two : vsharpEquiv.symm 2 = vZ := rfl

theorem sym3Hom_tauN : sym3Hom tauN = List.formPerm [0, 1, 2] := by
  have h0 : sym3Hom tauN 0 = 1 := by
    rw [sym3Hom_apply, vsharpEquiv_symm_zero, tauN_vX, vsharpEquiv_vY]
  have h1 : sym3Hom tauN 1 = 2 := by
    rw [sym3Hom_apply, vsharpEquiv_symm_one, tauN_vY, vsharpEquiv_vZ]
  have h2 : sym3Hom tauN 2 = 0 := by
    rw [sym3Hom_apply, vsharpEquiv_symm_two, tauN_vZ, vsharpEquiv_vX]
  refine Equiv.ext fun k => ?_
  fin_cases k
  · exact h0.trans (by decide)
  · exact h1.trans (by decide)
  · exact h2.trans (by decide)

theorem exists_swap_N :
    ∃ e : Ntwo, (e : Dfull) ∈ Ptwo ∧ e • vX = vX ∧ e • vY = vZ ∧ e • vZ = vY := by
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
  refine ⟨⟨iotaD e₀, Ptwo_le_Ntwo hP⟩, hP, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · change iotaD e₀ * xhat * (iotaD e₀)⁻¹ = xhat
    rw [← iotaD_xbar, ← map_inv, ← map_mul, ← map_mul, hx]
  · change iotaD e₀ * iotaD ybar * (iotaD e₀)⁻¹ = yhat
    rw [yhat, ← map_inv, ← map_mul, ← map_mul, ← xbar_mul_zbar,
      show e₀ * (xbar * zbar) * e₀⁻¹ = (e₀ * xbar * e₀⁻¹) * (e₀ * zbar * e₀⁻¹) by group, hx, he,
      ← xbar_mul_zbar, ← mul_assoc, xbar_mul_self, one_mul]
  · change iotaD e₀ * yhat * (iotaD e₀)⁻¹ = iotaD ybar
    rw [yhat, ← map_inv, ← map_mul, ← map_mul, he]

theorem closure_three : Subgroup.closure ({List.formPerm [0, 1, 2], Equiv.swap 1 2} :
    Set (Equiv.Perm (Fin 3))) = ⊤ := by
  have hnd : ([0, 1, 2] : List (Fin 3)).Nodup := by decide
  refine Equiv.Perm.closure_prime_cycle_swap (by decide) (List.isCycle_formPerm hnd (by decide))
    ?_ ⟨1, 2, by decide, rfl⟩
  rw [List.support_formPerm_of_nodup _ hnd (by decide)]
  decide

theorem sym3Hom_surjective :
    Function.Surjective sym3Hom := by
  obtain ⟨e, -, hx, hy, hz⟩ := exists_swap_N
  have ht : sym3Hom e = Equiv.swap 1 2 := by
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
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_three, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨tauN, sym3Hom_tauN⟩
  · exact ⟨e, ht⟩

theorem Ctwo_le_Ntwo : Ctwo ≤ Ntwo := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have h := (Subgroup.mem_centralizer_iff.1 hg) n hn
  rw [← h, mul_inv_cancel_right]
  exact hn

theorem ker_sym3Hom : sym3Hom.ker = Ctwo.subgroupOf Ntwo := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hfix : ∀ v : Vsharp, g • v = v := by
      intro v
      have := congrArg (fun σ : Equiv.Perm (Fin 3) => σ (vsharpEquiv v)) h
      simp only [sym3Hom_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply] at this
      exact vsharpEquiv.injective this
    rw [Ctwo, Subgroup.mem_centralizer_iff]
    intro d hd
    by_cases h1 : d = 1
    · rw [h1, one_mul, mul_one]
    · have := congrArg Subtype.val (hfix ⟨d, hd, h1⟩)
      rw [coe_smul_vsharp] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
  · intro h
    ext k
    rw [sym3Hom_apply, Equiv.Perm.one_apply]
    have hc := Subgroup.mem_centralizer_iff.1 h
    have hv : g • vsharpEquiv.symm k = vsharpEquiv.symm k := Subtype.ext (by
      rw [coe_smul_vsharp, ← hc _ (vsharpEquiv.symm k).2.1, mul_inv_cancel_right])
    rw [hv, Equiv.apply_symm_apply]

instance Ctwo_subgroupOf_normal : (Ctwo.subgroupOf Ntwo).Normal :=
  ker_sym3Hom ▸ sym3Hom.normal_ker

@[expose] noncomputable def ntwoQuotEquiv :
    Ntwo ⧸ Ctwo.subgroupOf Ntwo ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq ker_sym3Hom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective sym3Hom sym3Hom_surjective)

theorem natCard_Ntwo :
    Nat.card Ntwo = 22858846741463040 := by
  have h := (Ptwo.subgroupOf Ntwo).card_mul_index
  rw [index_Ptwo_Ntwo, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ptwo_le_Ntwo).toEquiv,
    natCard_Ptwo] at h
  omega

theorem natCard_Ctwo :
    Nat.card Ctwo = 3809807790243840 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Ctwo.subgroupOf Ntwo)
  rw [Nat.card_congr ntwoQuotEquiv.toEquiv, Nat.card_perm, Nat.card_fin,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ctwo_le_Ntwo).toEquiv, natCard_Ntwo] at h
  have h6 : Nat.factorial 3 = 6 := rfl
  rw [h6] at h
  omega

end CFSG.Monster.B.TwoA
