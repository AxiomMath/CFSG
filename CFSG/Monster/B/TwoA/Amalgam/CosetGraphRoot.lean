module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphRootCore
public import CFSG.Monster.B.TwoA.Amalgam.PointRoot

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

@[expose] def vStab
    (v : CVert) : Subgroup Shat where
  carrier := {s | cvMul v s = v}
  mul_mem' {a b} ha hb := by
    show cvMul v (a * b) = v
    rw [cvMul_mul, ha, hb]
  one_mem' := cvMul_one v
  inv_mem' {a} ha := by
    show cvMul v a⁻¹ = v
    conv_lhs => rw [← ha]
    rw [cvMul_inv_cancel]

theorem mem_vStab
    {v : CVert} {s : Shat} : s ∈ vStab v ↔ cvMul v s = v := Iff.rfl

theorem cvMul_mem_neighborSet
    {v : CVert} {y : Shat} (hy : y ∈ vStab v) {u : CVert}
    (hu : u ∈ cgraph.neighborSet v) : cvMul u y ∈ cgraph.neighborSet v := by
  have h := (cgraph_adj_cvMul v u y).2 hu
  rwa [mem_vStab.1 hy] at h

@[expose] def stabAct
    {v : CVert} (y : vStab v) (u : cgraph.neighborSet v) :
    cgraph.neighborSet v :=
  ⟨cvMul u y, cvMul_mem_neighborSet y.2 u.2⟩

theorem coe_stabAct
    {v : CVert} (y : vStab v) (u : cgraph.neighborSet v) :
    (stabAct y u : CVert) = cvMul u y := rfl

theorem mem_vStab_cv0
    {s : Shat} : s ∈ vStab cv0 ↔ (s : Dfull) ∈ Eam := cvMul_cv0_iff s

theorem conj_mem_Eam
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) {y : Shat}
    (hy : y ∈ vStab v) : ((s * y * s⁻¹ : Shat) : Dfull) ∈ Eam := by
  rw [← mem_vStab_cv0, mem_vStab, cvMul_mul, cvMul_mul, hs, mem_vStab.1 hy, ← hs,
    cvMul_inv_cancel]

@[expose] def stabToEam
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) : vStab v →* Eam where
  toFun y := ⟨((s * y * s⁻¹ : Shat) : Dfull), conj_mem_Eam hs y.2⟩
  map_one' := by
    apply Subtype.ext
    show ((s * (1 : Shat) * s⁻¹ : Shat) : Dfull) = 1
    rw [mul_one, mul_inv_cancel, OneMemClass.coe_one]
  map_mul' a b := by
    apply Subtype.ext
    show ((s * ((a : Shat) * b) * s⁻¹ : Shat) : Dfull) =
      ((s * a * s⁻¹ : Shat) : Dfull) * ((s * b * s⁻¹ : Shat) : Dfull)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem stabToEam_surjective
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    Function.Surjective (stabToEam hs) := by
  intro e
  have hy : s⁻¹ * toS e * s ∈ vStab v := by
    rw [mem_vStab, ← hs, ← cvMul_mul, show s * (s⁻¹ * toS e * s) = toS e * s by group,
      cvMul_mul, cvMul_cv0_toS]
  refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
  show ((s * (s⁻¹ * toS e * s) * s⁻¹ : Shat) : Dfull) = e
  rw [show s * (s⁻¹ * toS e * s) * s⁻¹ = toS e by group, coe_toS]

@[expose] def rhoV
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) {v : CVert} {s : Shat}
    (hs : cvMul cv0 s = v) : vStab v →* GStar :=
  θ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.zpowers cE')).comp (stabToEam hs))

theorem rhoV_surjective
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) {v : CVert} {s : Shat}
    (hs : cvMul cv0 s = v) : Function.Surjective (rhoV θ hs) := by
  intro γ
  obtain ⟨q, rfl⟩ := θ.surjective γ
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨y, hy⟩ := stabToEam_surjective hs e
  exact ⟨y, by simp only [rhoV, MonoidHom.coe_comp, Function.comp_apply, hy,
    QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]⟩

@[expose] def nbrShift
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    cgraph.neighborSet cv0 ≃ cgraph.neighborSet v where
  toFun u := ⟨cvMul u s, by
    have h := (cgraph_adj_cvMul cv0 u s).2 u.2
    rwa [hs] at h⟩
  invFun w := ⟨cvMul w s⁻¹, by
    have h := (cgraph_adj_cvMul v w s⁻¹).2 w.2
    have h2 : cvMul v s⁻¹ = cv0 := by rw [← hs, cvMul_inv_cancel]
    rw [h2] at h
    exact h⟩
  left_inv u := Subtype.ext (cvMul_inv_cancel _ _)
  right_inv w := Subtype.ext (cvMul_inv_cancel' _ _)

theorem coe_nbrShift
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) (u : cgraph.neighborSet cv0) :
    (nbrShift hs u : CVert) = cvMul u s := rfl

theorem coe_nbrShift_symm
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v)
    (w : cgraph.neighborSet v) : ((nbrShift hs).symm w : CVert) = cvMul w s⁻¹ := rfl

section General

variable (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar)
  (hx : θ (QuotientGroup.mk xhatEam) = rootStar)
  (hinj : ∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
    (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (e'⁻¹ * xhatEam * e'))
  (hcomm : ∀ e e' : Eam,
    ((∃ x, (vtx 0 (chamberOf e) ∩ vtx 3 x).Nonempty ∧ (vtx 0 (chamberOf e') ∩ vtx 3 x).Nonempty) ↔
      Commute (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE')
        (QuotientGroup.mk (e'⁻¹ * xhatEam * e'))))

@[expose] def rootV
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    cgraph.neighborSet v ≃ rootClass :=
  (nbrShift hs).symm.trans ((nbrEquiv a0_mem_Ehat a0_not_mem_N1).symm.trans
    (rootPtEquiv θ hx hinj))

include hinj in
theorem rootV_nbr
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) (e : Eam)
    (h : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈ cgraph.neighborSet v) :
    rootV θ hx hinj hs ⟨_, h⟩ = rootPt θ hx (Quotient.mk _ e) := by
  have e1 : (nbrShift hs).symm ⟨_, h⟩ = nbrEquiv a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e) :=
    Subtype.ext (by
      rw [coe_nbrShift_symm, coe_nbrEquiv]
      exact cvMul_inv_cancel (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s)
  rw [rootV, Equiv.trans_apply, Equiv.trans_apply, e1, Equiv.symm_apply_apply]
  rfl

include hinj hcomm in
theorem adj_iff_commute_rootV
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v)
    {u w : cgraph.neighborSet v} (hne : u ≠ w) :
    cgraph.Adj u w ↔ Commute (rootV θ hx hinj hs u : stdGroup) (rootV θ hx hinj hs w) := by
  set u₀ := (nbrEquiv a0_mem_Ehat a0_not_mem_N1).symm ((nbrShift hs).symm u)
  set w₀ := (nbrEquiv a0_mem_Ehat a0_not_mem_N1).symm ((nbrShift hs).symm w)
  have hu : (u : CVert) = cvMul (nbr a0_mem_Ehat a0_not_mem_N1 u₀) s := by
    rw [← coe_nbrEquiv, Equiv.apply_symm_apply, ← coe_nbrShift hs, Equiv.apply_symm_apply]
  have hw : (w : CVert) = cvMul (nbr a0_mem_Ehat a0_not_mem_N1 w₀) s := by
    rw [← coe_nbrEquiv, Equiv.apply_symm_apply, ← coe_nbrShift hs, Equiv.apply_symm_apply]
  have hne₀ : u₀ ≠ w₀ := fun h => hne (by
    have := congrArg (fun z => nbrShift hs (nbrEquiv a0_mem_Ehat a0_not_mem_N1 z)) h
    simpa [u₀, w₀] using this)
  rw [hu, hw, cgraph_adj_cvMul]
  exact adj_iff_commute_rootPt θ hx hcomm hne₀

theorem rhoV_apply {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) (y : vStab v) :
    rhoV θ hs y = rho0 θ (stabToEam hs y) := rfl

theorem toS_stabToEam
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) (y : vStab v) :
    toS (stabToEam hs y) = s * y * s⁻¹ := rfl

theorem nbrShift_symm_mk
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v)
    (u : cgraph.neighborSet v) :
    ∃ e : Eam, (u : CVert) = cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s := by
  obtain ⟨e, he⟩ := Quotient.mk_surjective
    ((nbrEquiv a0_mem_Ehat a0_not_mem_N1).symm ((nbrShift hs).symm u))
  refine ⟨e, ?_⟩
  rw [he, ← coe_nbrEquiv, Equiv.apply_symm_apply, ← coe_nbrShift hs, Equiv.apply_symm_apply]

include hinj in
theorem rootV_eq_of_coe
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) {u : cgraph.neighborSet v}
    {e : Eam} (hu : (u : CVert) = cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s) :
    rootV θ hx hinj hs u = rootPt θ hx (Quotient.mk _ e) := by
  have hmem : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈
      cgraph.neighborSet v := hu ▸ u.2
  rw [← rootV_nbr θ hx hinj hs e hmem]
  exact congrArg _ (Subtype.ext hu)

include hinj in
theorem inl_rootV_stabAct
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) (y : vStab v)
    (u : cgraph.neighborSet v) :
    SemidirectProduct.inl (rootV θ hx hinj hs (stabAct y u) : stdGroup) =
      (rhoV θ hs y)⁻¹ * SemidirectProduct.inl (rootV θ hx hinj hs u : stdGroup) * rhoV θ hs y := by
  obtain ⟨e, hu⟩ := nbrShift_symm_mk hs u
  have hyu : (stabAct y u : CVert) =
      cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ (e * stabToEam hs y))) s := by
    rw [coe_stabAct, hu, nbr_mk_mul, ← cvMul_mul, ← cvMul_mul, toS_stabToEam]
    congr 1
    group
  have h1 := rootV_eq_of_coe θ hx hinj hs hu
  have h2 := rootV_eq_of_coe θ hx hinj hs hyu
  calc (SemidirectProduct.inl (rootV θ hx hinj hs (stabAct y u) : stdGroup) : GStar)
      = SemidirectProduct.inl
          (rootPt θ hx (Quotient.mk _ (e * stabToEam hs y)) : stdGroup) :=
        congrArg (fun z : rootClass => (SemidirectProduct.inl (z : stdGroup) : GStar)) h2
    _ = (rho0 θ (stabToEam hs y))⁻¹ *
          (SemidirectProduct.inl (rootPt θ hx (Quotient.mk _ e) : stdGroup) : GStar) *
          rho0 θ (stabToEam hs y) := inl_rootPt_mk_mul θ hx e _
    _ = (rhoV θ hs y)⁻¹ * SemidirectProduct.inl (rootV θ hx hinj hs u : stdGroup) *
          rhoV θ hs y :=
        congrArg (fun z : rootClass => (rho0 θ (stabToEam hs y))⁻¹ *
          (SemidirectProduct.inl (z : stdGroup) : GStar) * rho0 θ (stabToEam hs y)) h1.symm

theorem clabel_eq_conj {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) :
    clabel v = (s : Dfull)⁻¹ * cQ * s := by
  rw [← hs, clabel_cvMul, clabel_cv0]

include θ hx in
theorem kernel_iff
    {v : CVert} {s : Shat} (hs : cvMul cv0 s = v) (y : Shat) :
    (cvMul v y = v ∧ ∀ u ∈ cgraph.neighborSet v, cvMul u y = u) ↔
      (y : Dfull) ∈ Subgroup.zpowers (clabel v) := by
  rw [clabel_eq_conj hs]
  have hconj : ∀ n : ℤ, ((s : Dfull)⁻¹ * cQ * s) ^ n = (s : Dfull)⁻¹ * cQ ^ n * s := by
    intro n
    have h := conj_zpow (i := n) (a := (s : Dfull)⁻¹) (b := cQ)
    rwa [inv_inv] at h
  constructor
  · rintro ⟨hy, hfix⟩
    set f := stabToEam hs ⟨y, hy⟩
    have hf : ∀ e : Eam, cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) (toS f) =
        nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e) := by
      intro e
      have hmem := (nbrShift hs (nbrEquiv a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e))).2
      have h1 := hfix _ hmem
      rw [coe_nbrShift, coe_nbrEquiv] at h1
      show cvMul _ (s * y * s⁻¹) = _
      rw [cvMul_mul, cvMul_mul, h1, cvMul_inv_cancel]
    have hk := (act_trivial_iff θ hx f).1 hf
    rw [mem_zpowers_subtype_iff] at hk
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hk
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [hconj n]
    have hn' : cQ ^ n = (s : Dfull) * y * (s : Dfull)⁻¹ := hn
    rw [hn']
    group
  · intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [hconj n] at hn
    have hsy : ((s * y * s⁻¹ : Shat) : Dfull) = cQ ^ n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hn]
      group
    have hE : ((s * y * s⁻¹ : Shat) : Dfull) ∈ Eam := by
      rw [hsy]
      exact Eam.zpow_mem cQ_mem_Eam n
    have hstab : cvMul cv0 (s * y * s⁻¹) = cv0 := (cvMul_cv0_iff _).2 hE
    have hv : cvMul v y = v := by
      rw [← hs, ← cvMul_mul, show s * y = (s * y * s⁻¹) * s by group, cvMul_mul, hstab]
    refine ⟨hv, fun u hu => ?_⟩
    set f : Eam := ⟨_, hE⟩
    have hfz : f ∈ Subgroup.zpowers cE' := by
      rw [mem_zpowers_subtype_iff]
      exact Subgroup.mem_zpowers_iff.2 ⟨n, hsy.symm⟩
    obtain ⟨e, he⟩ := Quotient.mk_surjective
      ((nbrEquiv a0_mem_Ehat a0_not_mem_N1).symm ((nbrShift hs).symm ⟨u, hu⟩))
    have hu' : u = cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s := by
      rw [he, ← coe_nbrEquiv, Equiv.apply_symm_apply, ← coe_nbrShift hs, Equiv.apply_symm_apply]
    have h1 := (act_trivial_iff θ hx f).2 hfz e
    have htf : toS f = s * y * s⁻¹ := rfl
    rw [hu', ← cvMul_mul, show s * y = (s * y * s⁻¹) * s by group, cvMul_mul, ← htf, h1]

theorem orderOf_clabel
    (v : CVert) : orderOf (clabel v) = 2 := by
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
  rw [clabel_eq_conj hs]
  have hc : orderOf cQ = 2 := orderOf_eq_prime (by rw [sq]; exact cQ_mul_self) cQ_ne_one
  rw [← hc]
  exact (SemiconjBy.orderOf_eq (s : Dfull)⁻¹ (by unfold SemiconjBy; group)).symm

include θ hx hcomm in
theorem adj_iff_common_vtx_shift
    (s : Shat) {u w : P1Cos} (hne : u ≠ w) :
    cgraph.Adj (cvMul (nbr a0_mem_Ehat a0_not_mem_N1 u) s)
        (cvMul (nbr a0_mem_Ehat a0_not_mem_N1 w) s) ↔
      ∃ x, (ptMap u ∩ vtx 3 x).Nonempty ∧ (ptMap w ∩ vtx 3 x).Nonempty := by
  rw [cgraph_adj_cvMul]
  exact adj_iff_common_vtx θ hx hcomm hne

end General

theorem native_coset_graph_exact_root_local_geometry :
    ∃ θ₀ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar, θ₀ (QuotientGroup.mk xhatEam) = rootStar ∧
      ∀ v : CVert, ∃ (s : Shat) (hs : cvMul cv0 s = v) (iv : cgraph.neighborSet v ≃ rootClass),
        (∀ (e : Eam) (h : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s ∈
            cgraph.neighborSet v),
          SemidirectProduct.inl (iv ⟨_, h⟩ : stdGroup) = θ₀ (QuotientGroup.mk (xconj e))) ∧
        (∀ u w : cgraph.neighborSet v, u ≠ w →
          (cgraph.Adj u w ↔ Commute (iv u : stdGroup) (iv w))) ∧
        (∀ (y : vStab v) (u : cgraph.neighborSet v),
          SemidirectProduct.inl (iv (stabAct y u) : stdGroup) =
            (rhoV θ₀ hs y)⁻¹ * SemidirectProduct.inl (iv u : stdGroup) * rhoV θ₀ hs y) ∧
        Function.Surjective (rhoV θ₀ hs) ∧
        (∀ y : Shat, (cvMul v y = v ∧ ∀ u ∈ cgraph.neighborSet v, cvMul u y = u) ↔
          (y : Dfull) ∈ Subgroup.zpowers (clabel v)) ∧
        orderOf (clabel v) = 2 ∧
        ∀ u w : P1Cos, u ≠ w →
          (cgraph.Adj (cvMul (nbr a0_mem_Ehat a0_not_mem_N1 u) s)
              (cvMul (nbr a0_mem_Ehat a0_not_mem_N1 w) s) ↔
            ∃ x, (ptMap u ∩ vtx 3 x).Nonempty ∧ (ptMap w ∩ vtx 3 x).Nonempty) := by
  obtain ⟨θ, -, -, -, -, -, hx, -, hinj, hcomm⟩ := native_F4_point_root_involution_intertwiner
  refine ⟨θ, hx, fun v => ?_⟩
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
  refine ⟨s, hs, rootV θ hx hinj hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e h
    have h1 := rootV_nbr θ hx hinj hs e h
    have h2 := inl_rootPt_mk θ hx e
    calc (SemidirectProduct.inl (rootV θ hx hinj hs ⟨_, h⟩ : stdGroup) : GStar)
        = SemidirectProduct.inl (rootPt θ hx (Quotient.mk _ e) : stdGroup) :=
          congrArg (fun z : rootClass => (SemidirectProduct.inl (z : stdGroup) : GStar)) h1
      _ = rho0 θ (xconj e) := h2
      _ = θ (QuotientGroup.mk (xconj e)) := rho0_apply θ _
  · intro u w hne
    exact adj_iff_commute_rootV θ hx hinj hcomm hs hne
  · intro y u
    exact inl_rootV_stabAct θ hx hinj hs y u
  · exact rhoV_surjective θ hs
  · exact kernel_iff θ hx hs
  · exact orderOf_clabel v
  · intro u w hne
    exact adj_iff_common_vtx_shift θ hx hcomm s hne

end CFSG.Monster.B.TwoA.Amalgam
